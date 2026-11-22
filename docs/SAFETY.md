# Safety Scope, Trusted Computing Base, and UB Exceptions

This document defines what the safety theorems in `zlib-lean` prove, what assumptions sit outside the Lean kernel, and which C pointer-arithmetic rules are modeled permissively.

## 1. Safety Scope and Preconditions

The formal safety claim covers executions of the Lean 4 model of patched zlib (`1.4.0.1-motley` at `617e19a` plus the 6 patches in [pins.json](../pins.json)) configured for the default x86-64 Linux LP64 static library build. On valid caller inputs, each safety goal establishes which faults (`Fault.ub` or `Fault.outOfFuel`) are excluded, which caller and internal regions may be modified, which allocations are preserved or freed, and when calls terminate.

| Area | Scope & Preconditions |
| --- | --- |
| Source & platform | Targets the pinned zlib revision and 6 patches built as a static x86-64 Linux LP64 library. Where `ByteObjectsFit` applies, each byte allocation is smaller than `2^63` bytes ([pins.json](../pins.json), [PlatformMemory.lean](../ZlibF/Spec/Common/PlatformMemory.lean)). |
| Allocator & buffers | Models the default allocator including allocation failures; custom caller allocators (`zalloc`/`zfree`) are outside scope. Goals state required buffer lengths, writability, and separation ([Memory.lean](../ZlibF/Spec/Common/Memory.lean)). |
| Single-object & disjoint multi-stream histories | Single-object contracts follow one stream or gzip handle from initialization or open, permitting caller buffer updates allowed by the frame condition between calls ([Sequences.lean](../ZlibF/Spec/Safety/Sequences.lean), [GzSafety.lean](../ZlibF/Spec/Safety/GzSafety.lean)). Sequential interleaving of multiple distinct `z_stream` objects (`inflate` and/or `deflate`) with disjoint owned blocks (`StreamDisjoint`, `ExternalWriteSafe`) is machine-checked in [MultiStream.lean](../ZlibF/Spec/Safety/MultiStream.lean). Concurrent OS-thread execution / data races and interleaved `gzFile` handles remain out of scope. |
| Callback decoder | `inflateBack` sequence safety requires terminating callbacks that respect buffer ownership and preserve the window, with strictly fewer than `2^48` input bytes per call ([Sequences.lean](../ZlibF/Spec/Safety/Sequences.lean)). |
| Gzip I/O & read budgets | For `gzread`, `gzfread`, `gzgetc`, `gzgetc_`, `gzgets`, and `gzungetc`, `Fault.ub` is excluded unconditionally. Proving return and excluding `Fault.outOfFuel` on a reachable handle additionally requires a nonnegative file descriptor with a read budget below `2^61` bytes; null-handle refusals and the buffered-output branch of `gzgetc` return without this budget. Writes assume a nonempty OS write either fails or advances ([gz.inv-model.lean](../ZlibF/Proof/gz.inv-model.lean), [GzInv.lean](../ZlibF/Spec/Common/GzInv.lean)). |
| Formatted output | `gzprintf` and `gzvprintf` require the C caller to supply valid format strings and matching variadic arguments without `%n`. The external formatter model bounds writes and reads its return status from the environment without checking C variadic type mismatches ([gzfs.lean](../ZlibF/Zlib/gzfs.lean)). |

### Using the Safety Theorems

Import [ZlibF/Results.lean](../ZlibF/Results.lean) to access the baseline whole-library entry point [`whole_library_safety`](../ZlibF/Results.lean) (which dispatches over every documented `PublicEntry` and single-object `StreamProtocol`) as well as [`extended_library_safety`](../ZlibF/Results.lean) (which adds the pointer-cell `CAbiCompanion` contracts for `compress*_c` and the `MultiStreamContract` compositionality theorems), defined in [WholeLibrary.lean](../ZlibF/Spec/Safety/WholeLibrary.lean):

```lean
import ZlibF.Results

open ZlibF.Results ZlibF.Spec.Public

example : Goal.compressBound_z := whole_library_safety.1 .compressBound_z
example : Goal.inflateCopy_safety := whole_library_safety.1 .inflateCopy
example : Goal.gz_sequence_safety := whole_library_safety.2 .gzip

example : Goal.compress2_c_safety := extended_library_safety.2.1 .compress2_c
example : Goal.multi_stream_step_safety := extended_library_safety.2.2 .stepSafety
```

To inspect an individual API contract:

1. Look up its `safety_goal` in [tests/public-api.json](../tests/public-api.json).
2. Read the predicate under `ZlibF/Spec/Safety/` (for `compressBound` and `compressBound_z`, their pure size-bound contracts in [Queries.lean](../ZlibF/Spec/Functional/Queries.lean) serve directly as their safety goals).
3. Check its proof and required entry in [ZlibF/Results.lean](../ZlibF/Results.lean).

Running `make library-safety` replays all proofs and runs both [check_public_safety.py](../tools/check_public_safety.py) (matching `PublicEntry`, `StreamProtocol`, the compiled `Call.execute` dispatcher, `tests/public-api.json`, and patched `zlib.h`) and [check_baseline_equiv.py](../tools/check_baseline_equiv.py) (confirming the baseline specification files and required baseline goals remain unchanged relative to commit `85cd20c`).

### End-to-End Safety Specification Walkthrough for C Auditors

For C auditors reading the Lean goals without prior `Std.WP` / `ZlibF` context, here is how concrete `zlib.h` prototypes map to Lean predicates:

1. **One-shot C-ABI compression (`int compress2(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen, int level)`)**:
   - The baseline goal `Goal.compress2_safety` ([Utilities.lean](../ZlibF/Spec/Safety/Utilities.lean), via `CompressorSafety` in [Common/Utilities.lean](../ZlibF/Spec/Common/Utilities.lean)) lifts the `*destLen` out-parameter to `Option UInt64`; the C-ABI companion `Goal.compress2_c_safety` ([UtilitiesCAbi.lean](../ZlibF/Spec/Safety/UtilitiesCAbi.lean), via `CompressorCSafety`) takes the raw pointer `destLen : BPtr` directly as lowered to C.
   - Preconditions on entry heap `h`:
     - `Fresh h` and `Zlib.Deflate.Spec.Uniq h`: allocator freshness and distinctness of stream/state object identities.
     - `LibraryGlobals h` and `ByteObjectsFit h`: global tables are resident and every byte object stays below `2^63` bytes (`PTRDIFF_MAX` platform bound).
     - `LengthCell h destLen capacity` (`8`-byte writable/readable `uLongf` cell holding `capacity`), `Bytes h source n.toNat xs` (readable `sourceLen` bytes matching `xs` when `source ≠ NULL`), `Writable h dest capacity.toNat` (writable output buffer when `dest ≠ NULL`), and pairwise separation `Separate` between `source`, `dest`, and `destLen`.
   - Postconditions established for every such input:
     - `C.run (compress2_c dest destLen source n level) h = .ok (rc, after)`: terminates in `C.M` with zero `Fault.ub` and zero `Fault.outOfFuel`.
     - Invalid inputs (`compressRejected`: `source == NULL && sourceLen != 0`, `dest == NULL && *destLen != 0`) return `Z_STREAM_ERROR` without mutating existing objects (`SameObjectsUpToTableShape h after`).
     - Valid inputs update at most `dest` (`Store h dest out h₁` with `out.length ≤ capacity.toNat`) and `*destLen` (`Store h₁ destLen (lengthBytes got) expected`), free all temporary `deflate` allocations (`SameObjectsUpToTableShape expected after`), and return `Z_MEM_ERROR` only if an allocation actually failed (`AllocationFailed h after`).

2. **Stateful stream step (`int inflate(z_streamp strm, int flush)`) and multi-stream interleaving**:
   - `Goal.inflate_safety` ([Streams.lean](../ZlibF/Spec/Safety/Streams.lean), via `StreamCallSafe` / `StreamCallDomain`) handles two C situations: invalid handles (`RefusedInflate`, e.g., `NULL` or inconsistent state) fail cleanly with `Z_STREAM_ERROR`; valid handles (`StreamReachable .inflate h r`, `StreamArguments h r call`, `ByteObjectsFit h`) return `.ok`, preserve `StreamInvariant .inflate`, restrict mutations via `BufferFrame` ([History.lean](../ZlibF/Spec/Common/History.lean)) strictly to `StreamRoot r`, `StreamOwned h r`, `StreamHeaderRecord`, and declared caller write slices `StreamWriteRegions h r call`, and track every internal `alloc`/`free` via `LiveChange` ([Initialisation.lean](../ZlibF/Spec/Common/Initialisation.lean)) so no internal block is leaked or double-freed.
   - `Goal.multi_stream_init_disjoint`, `Goal.multi_stream_step_safety`, `Goal.multi_stream_end_safety`, and `Goal.multi_stream_nonvacuity` ([MultiStream.lean](../ZlibF/Spec/Safety/MultiStream.lean)) extend this to two distinct streams `r₁ ≠ r₂` sharing a single heap `h`: when `StreamDisjoint h r₁ r₂` holds (pairwise disjoint owned allocations) and `ExternalWriteSafe h r₁ r₂ call` guarantees caller-provided output buffers for `r₁` do not alias `r₂`'s owned blocks, stepping or ending `r₁` acts as a valid `Rebuffer` on `r₂`, preserves `r₂`'s record, owned allocation set, invariant, and reachability, and preserves `StreamDisjoint`.

3. **Distinguishing `Fault.ub` exclusion from `Fault.outOfFuel` termination**:
   - In [Monad.lean](../ZlibF/Runtime/Monad.lean), `C.Fault` has two constructors: `Fault.ub` (undefined behavior, e.g., out-of-bounds pointer access, signed overflow, shift UB) and `Fault.outOfFuel` (exhausting the loop counter `C.fuel = 2 ^ 64`).
   - Whenever a goal concludes `C.run m h = .ok (...)` on its domain, **both** `Fault.ub` and `Fault.outOfFuel` are ruled out (the call returns). By contrast, when a contract states bounded-budget termination (e.g., `inflateBack` with `< 2^48` total input bytes, or `gzread`/`gzgets`/`gzungetc` with a nonnegative fd and read budget `< 2^61` bytes), `Fault.ub` is excluded unconditionally while exclusion of `Fault.outOfFuel` relies on the stated input/read budget.

## 2. Trusted Computing Base (TCB)

Running `make proof` builds `ZlibF` with warnings treated as errors and replays [ZlibF/Results.lean](../ZlibF/Results.lean) in a fresh kernel via `leanchecker --fresh ZlibF.Results`. The registry checker ([ResultsCheck.lean](../ZlibF/ResultsCheck.lean)) ensures that:

- Every proved safety theorem has a type syntactically equal to its declared `Goal.*` (**134** proved goals, **0** unproved, **109** required).
- Only the standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) appear in any dependency chain.
- Every `Goal.*` in the safety scope (`ZlibF.Spec.Safety.*`, `compressBound`, `compressBound_z`) is accounted for.

Two complementary assurance layers guard against spec drift and lowering errors:

- **Baseline equivalence verification**: [check_baseline_equiv.py](../tools/check_baseline_equiv.py) verifies that all **17** baseline safety spec files (**122** `Goal.*` declarations), **43** `Spec/Common` files, **4** core `Runtime` files, and all baseline `proved`/`required` entries in [ZlibF/Results.lean](../ZlibF/Results.lean) match commit `85cd20c` token-for-token outside comments/docstrings (`whole_library_safety`, `PublicEntry`, and `StreamProtocol` are unchanged). [LemmaEquivalence.lean](../tests/LemmaEquivalence.lean) additionally checks kernel-level definitional/logical equivalence between legacy monolithic helpers (split `Libc`, `inflateCopy` window proofs, `crc32` byte/word helpers, `OkOn` ↔ `Std.WP` triple bridge) and the current modularized definitions.
- **Formal C99 AST semantics & soundness for lowered kernels**: [Semantics.lean](../Lean2C/Semantics.lean) defines a total C99 LP64 evaluator (`evalValue`, `execStmt`, `runCFn`) with explicit UB guards (`Fault.ub` on shift bounds/negatives, signed overflow, division by zero, and out-of-bounds memory access). [Soundness.lean](../Lean2C/Soundness.lean) and [CSourceSoundness.lean](../tests/CSourceSoundness.lean) prove C99 §6.5.7 shift UB-freedom/bit-exactness, `load8`/`load64`/`store8`/`store64` and `while`/`do-while` simulation, and end-to-end `runCFn` soundness & safety transfer for the live `lowerStmts?` C ASTs of `compressBound_z`, `compressBound`, `zlibCompileFlags`, `byte_swap`, and `adler32_combine_`.

Applying these theorems to compiled C binaries still relies on three assumptions outside the Lean kernel:

1. **Runtime & OS/libc model faithfulness**: Fidelity of the modeled heap, pointer bounds, `malloc`/`free`/`memcpy`/`memmove`/`memset`/`strlen`, and POSIX `gz*` I/O ([Libc.lean](../ZlibF/Runtime/Libc.lean), [LibcMemory.lean](../ZlibF/Runtime/LibcMemory.lean), [LibcAllocation.lean](../ZlibF/Runtime/LibcAllocation.lean), [LibcCString.lean](../ZlibF/Runtime/LibcCString.lean), [gzfs.lean](../ZlibF/Zlib/gzfs.lean)).
2. **Source-level C aliasing & unmodeled constructs**: Where the Lean model decomposes memory accesses (for instance, byte-by-byte word assembly in [crc32.c.lean](../ZlibF/Zlib/crc32.c.lean)), C strict-aliasing compliance in the C code remains a manual review obligation.
3. **Remaining Lean-to-C emission, rendering, and compilation gap**: While [Lower.lean](../Lean2C/Lower.lean), [Semantics.lean](../Lean2C/Semantics.lean), and [Soundness.lean](../Lean2C/Soundness.lean) formally verify the lowered C99 AST for key standalone functions, C text pretty-printing (`renderStmts` / `renderBody` in [C.lean](../Lean2C/C.lean)), the remaining **10 / 15** unlowered translation units (which still rely on reference C splicing), and downstream C compilation (`clang -O2`) remain in the TCB. `Lean2C` emits compilable standalone C for **5 / 15** units (`adler32.c`, `compress.c`, `gzclose.c`, `uncompr.c`, `zutil.c`), **3** headers (`crc32.h`, `inffixed.h`, `trees.h`), and `_Static_assert` ABI layout checks for **10** core structs (**163** fields), and `make binary` / `make audit` / `make differential` serve as build & runtime checks rather than an end-to-end verified C compiler.

## 3. Manual Undefined-Behavior Exceptions

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
