# Safety Scope, Trusted Computing Base, and UB Exceptions

This document defines what the safety theorems in `zlib-lean` prove, what assumptions sit outside the Lean kernel, and which C pointer-arithmetic rules are modeled permissively.

## 1. Safety Scope and Preconditions

The formal safety claim covers executions of the Lean 4 model of patched zlib (`1.4.0.1-motley` at `617e19a` plus the 6 patches in [pins.json](../pins.json)) configured for the default x86-64 Linux LP64 static library build. On valid caller inputs, each safety goal establishes which faults (`Fault.ub` or `Fault.outOfFuel`) are excluded, which caller and internal regions may be modified, which allocations are preserved or freed, and when calls terminate.

| Area | Scope & Preconditions |
| --- | --- |
| Source & platform | Targets the pinned zlib revision and 6 patches built as a static x86-64 Linux LP64 library. Where `ByteObjectsFit` applies, each byte allocation is smaller than `2^63` bytes ([pins.json](../pins.json), [PlatformMemory.lean](../ZlibF/Spec/Common/PlatformMemory.lean)). |
| Allocator & buffers | Models the default allocator including allocation failures; custom caller allocators (`zalloc`/`zfree`) are outside scope. Goals state required buffer lengths, writability, and separation ([Memory.lean](../ZlibF/Spec/Common/Memory.lean)). |
| Single-object histories | Sequence contracts follow one stream or gzip handle from initialization or open, permitting caller buffer updates allowed by the frame condition between calls. Multi-object or concurrent histories are out of scope ([Sequences.lean](../ZlibF/Spec/Safety/Sequences.lean), [GzSafety.lean](../ZlibF/Spec/Safety/GzSafety.lean)). |
| Callback decoder | `inflateBack` sequence safety requires terminating callbacks that respect buffer ownership and preserve the window, with strictly fewer than `2^48` input bytes per call ([Sequences.lean](../ZlibF/Spec/Safety/Sequences.lean)). |
| Gzip I/O & read budgets | For `gzread`, `gzfread`, `gzgetc`, `gzgetc_`, `gzgets`, and `gzungetc`, `Fault.ub` is excluded unconditionally. Proving return and excluding `Fault.outOfFuel` on a reachable handle additionally requires a nonnegative file descriptor with a read budget below `2^61` bytes; null-handle refusals and the buffered-output branch of `gzgetc` return without this budget. Writes assume a nonempty OS write either fails or advances ([gz.inv-model.lean](../ZlibF/Proof/gz.inv-model.lean), [GzInv.lean](../ZlibF/Spec/Common/GzInv.lean)). |
| Formatted output | `gzprintf` and `gzvprintf` require the C caller to supply valid format strings and matching variadic arguments without `%n`. The external formatter model bounds writes and reads its return status from the environment without checking C variadic type mismatches ([gzfs.lean](../ZlibF/Zlib/gzfs.lean)). |

### Using the Safety Theorems

Import [ZlibF/Results.lean](../ZlibF/Results.lean) to access [`whole_library_safety`](../ZlibF/Results.lean), which dispatches over any documented public entry point (`PublicEntry`) or single-object protocol (`StreamProtocol`) defined in [WholeLibrary.lean](../ZlibF/Spec/Safety/WholeLibrary.lean):

```lean
import ZlibF.Results

open ZlibF.Results ZlibF.Spec.Public

example : Goal.compressBound_z := whole_library_safety.1 .compressBound_z
example : Goal.inflateCopy_safety := whole_library_safety.1 .inflateCopy
example : Goal.gz_sequence_safety := whole_library_safety.2 .gzip
```

To inspect an individual API contract:

1. Look up its `safety_goal` in [tests/public-api.json](../tests/public-api.json).
2. Read the predicate under `ZlibF/Spec/Safety/` (for `compressBound` and `compressBound_z`, their pure size-bound contracts in [Queries.lean](../ZlibF/Spec/Functional/Queries.lean) serve directly as their safety goals).
3. Check its proof and required entry in [ZlibF/Results.lean](../ZlibF/Results.lean).

Running `make library-safety` replays all proofs and verifies via [check_public_safety.py](../tools/check_public_safety.py) that `PublicEntry`, `StreamProtocol`, the compiled `Call.execute` dispatcher, the API inventory, and the patched `zlib.h` header stay in sync.

## 2. Trusted Computing Base (TCB)

Running `make proof` builds `ZlibF` with warnings treated as errors and replays [ZlibF/Results.lean](../ZlibF/Results.lean) in a fresh kernel via `leanchecker --fresh ZlibF.Results`. The registry checker ([ResultsCheck.lean](../ZlibF/ResultsCheck.lean)) ensures that:

- Every proved safety theorem has a type syntactically equal to its declared `Goal.*` (**125** proved goals, **0** unproved, **100** required).
- Only the standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) appear in any dependency chain.
- Every `Goal.*` in the safety scope (`ZlibF.Spec.Safety.*`, `compressBound`, `compressBound_z`) is accounted for.

Applying these theorems to C relies on three assumptions outside the Lean kernel:

1. **Runtime & OS/libc model faithfulness**: Fidelity of the modeled heap, pointer bounds, `malloc`/`free`/`memcpy`/`memmove`/`memset`/`strlen`, and POSIX `gz*` I/O ([Libc.lean](../ZlibF/Runtime/Libc.lean), [LibcMemory.lean](../ZlibF/Runtime/LibcMemory.lean), [LibcAllocation.lean](../ZlibF/Runtime/LibcAllocation.lean), [LibcCString.lean](../ZlibF/Runtime/LibcCString.lean), [gzfs.lean](../ZlibF/Zlib/gzfs.lean)).
2. **Source-level C aliasing & unmodeled constructs**: Where the Lean model decomposes memory accesses (for instance, byte-by-byte word assembly in [crc32.c.lean](../ZlibF/Zlib/crc32.c.lean)), C strict-aliasing compliance in the C code remains a manual review obligation.
3. **Current Lean-to-C translation gap**: Lean-to-C lowering in `Lean2C` is still under active development. Currently, `Lean2C` emits compilable standalone C for **5 / 15** units (`adler32.c`, `compress.c`, `gzclose.c`, `uncompr.c`, `zutil.c`), **3** headers (`crc32.h`, `inffixed.h`, `trees.h`), and `_Static_assert` ABI layout checks for **10** core structs (**163** fields), while **10 / 15** translation units are not yet independently compiled from Lean. Accordingly, this repository does **not** claim binary equivalence or full C AST equivalence with upstream C `libz.a`; `make binary`, `make audit`, and `make differential` serve as development diagnostics rather than an end-to-end verified compiler.

## 3. C Undefined-Behavior Exceptions

No-fault theorems exclude `Fault.ub` as defined by the Lean pointer runtime ([Ptr.lean](../ZlibF/Runtime/Ptr.lean)). Two C17 pointer-arithmetic rules are intentionally given defined semantics in the Lean model, so C behavior at those call sites relies on target-compiler assumptions outside the Lean guarantee.

### Accepted Pointer-Arithmetic Exceptions

| Operation | Modeled Semantics | Patched zlib Call Sites |
| --- | --- | --- |
| `Ptr.add p 0` | Returns `(p, h)` without checking allocation liveness, treating zero-byte pointer advance as a no-op for any pointer value (including `NULL` or a pointer into a freed buffer). | `gzseek64` ([gzlib.c.lean](../ZlibF/Zlib/gzlib.c.lean)) and `gz_skip_have` ([gzread.c.lean](../ZlibF/Zlib/gzread.c.lean)) can execute `state->x.next += n` with `n == 0` when `x.next` is unwritten or refers to an expired caller buffer. |
| `Ptr.diff .null .null` | Returns signed `0` and leaves the heap unchanged (matching C++ semantics, whereas C17/C23 leave `NULL - NULL` undefined). | `compress2_z` ([compress.c.lean](../ZlibF/Zlib/compress.c.lean), [Utilities.lean](../ZlibF/Spec/Common/Utilities.lean)) evaluates `stream.next_out - dest` with both operands `NULL` when `*destLen == 0` and `dest == NULL`. |

### Other Null-Pointer & Initialization Rules

| Case | Modeled Semantics & Reading of Safety Theorems | Reference |
| --- | --- | --- |
| Invalid dereference or arithmetic | Dereferencing `NULL`, adding a nonzero offset to `NULL`, subtracting `NULL` from a non-`NULL` pointer, and subtracting pointers from distinct allocations all raise `Fault.ub` and are excluded by no-fault proofs. | [Ptr.lean](../ZlibF/Runtime/Ptr.lean) |
| Zero-length libc calls | Modeled `memcpy`, `memmove`, and `memset` fault on `NULL` pointers even when `n == 0`; `free(NULL)` is a defined no-op. | [LibcMemory.lean](../ZlibF/Runtime/LibcMemory.lean) · [LibcAllocation.lean](../ZlibF/Runtime/LibcAllocation.lean) |
| Null inputs permitted by API | `crc32` accepts `NULL` buffers at any length; `adler32` accepts `NULL` only at length `0`; `gzgetc(NULL)` fails safely for the C function, though callers of the `gzgetc` macro dereference the handle before calling the function. | [Checksums.lean](../ZlibF/Spec/Common/Checksums.lean) · [GzRefusal.lean](../ZlibF/Spec/Safety/GzRefusal.lean) |
| Unwritten struct fields | Fresh modeled records initialize pointer fields to `NULL`, whereas C leaves uninitialized fields indeterminate; initialization before read/free remains a C review item. | [Schema.lean](../ZlibF/Runtime/Schema.lean) |
