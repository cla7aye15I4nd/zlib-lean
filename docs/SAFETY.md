# Safety Claim, Trusted Base, and UB Exceptions

This document defines the maintained safety scope of `zlib-lean`, explains what is trusted when reading a Lean safety theorem as a claim about C, and records every accepted undefined-behavior (UB) exception.

## 1. Safety Scope and Assumptions

The claim covers executions of the Lean 4 model of patched zlib (`1.4.0.1-motley` at `617e19a` plus the 6 patches in [pins.json](../pins.json)) for the default x86-64 Linux LP64 static build. On valid caller inputs, safety goals prove which faults (`Fault.ub` / `Fault.outOfFuel`) are excluded, which memory regions may be modified, which allocations are kept or freed, and when calls return.

| Condition | Effect on the claim |
| --- | --- |
| Source & platform | Targets the pinned zlib commit + 6 patches built as a default x86-64 Linux LP64 static library. Where `ByteObjectsFit` is assumed, each byte object is smaller than `2^63` bytes ([pins.json](../pins.json), [PlatformMemory.lean](../ZlibF/Spec/Common/PlatformMemory.lean)). |
| Allocation & caller memory | Covers the default allocator including allocation failure; custom allocators are out of scope. Each goal states required buffer extents, writability, and separation ([Memory.lean](../ZlibF/Spec/Common/Memory.lean)). |
| Stream history | Sequence goals track a single stream or gzip handle from initialization/open, allowing caller buffer updates permitted by the caller frame between calls. Cross-object or concurrent histories are out of scope ([Sequences.lean](../ZlibF/Spec/Safety/Sequences.lean), [GzSafety.lean](../ZlibF/Spec/Safety/GzSafety.lean)). |
| Callback decoder | `inflateBack` sequence safety requires returning callbacks that respect ownership and preserve the window, with total input per call under `2^48` bytes ([Sequences.lean](../ZlibF/Spec/Safety/Sequences.lean)). |
| Gzip I/O | For `gzread`, `gzfread`, `gzgetc`, `gzgetc_`, `gzgets`, and `gzungetc`, `Fault.ub` is excluded unconditionally; excluding `Fault.outOfFuel` and proving return additionally require a nonnegative descriptor with fewer than `2^61` bytes left in its read budget. Writes assume a nonempty OS write either fails or makes progress ([gz.inv-model.lean](../ZlibF/Proof/gz.inv-model.lean), [GzInv.lean](../ZlibF/Spec/Common/GzInv.lean)). |
| Formatted output | `gzprintf` and `gzvprintf` assume the C caller passes a defined format/argument combination without `%n`. The external formatter model bounds writes and models return values from the environment, without checking format/argument type mismatches ([gzfs.lean](../ZlibF/Zlib/gzfs.lean)). |

### Tracing a Public API

1. Look up the function's `safety_goal` in [tests/public-api.json](../tests/public-api.json).
2. Read the goal predicate under [ZlibF/Spec/Safety/](../ZlibF/Spec/Safety/Streams.lean) (for `compressBound` and `compressBound_z`, the pure bound contracts in [Queries.lean](../ZlibF/Spec/Functional/Queries.lean) serve directly as their safety goals).
3. Verify its registered theorem and required status in [ZlibF/Results.lean](../ZlibF/Results.lean).

## 2. Trusted Computing Base (TCB)

Running `make proof` builds `ZlibF` with warnings as errors and replays [ZlibF/Results.lean](../ZlibF/Results.lean) in a fresh Lean kernel (`leanchecker --fresh ZlibF.Results`). The registry checker ([ResultsCheck.lean](../ZlibF/ResultsCheck.lean)) verifies that:

- Every proved safety theorem's type is syntactically equal to its declared `Goal.*` (`124` proved safety goals, `0` remaining, `99` required).
- Only the three standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) appear in any proof dependency chain.
- Every `Goal.*` in the safety scope (`ZlibF.Spec.Safety.*`, `compressBound`, `compressBound_z`) is accounted for.

Transferring a Lean theorem to the compiled C binary depends on three boundary assumptions outside the Lean kernel:

1. **Runtime & libc/OS model faithfulness**: Models of heap tables, byte/struct pointers, `malloc`/`free`/`memcpy`/`memset`/`strlen`, and POSIX `gz*` I/O ([Libc.lean](../ZlibF/Runtime/Libc.lean), [gzfs.lean](../ZlibF/Zlib/gzfs.lean)).
2. **Source-level C aliasing & unmodeled constructs**: For example, [crc32.c.lean](../ZlibF/Zlib/crc32.c.lean) assembles words from byte reads, leaving C strict-aliasing rules for word-pointer casts to source review.
3. **Model-to-C/Binary correspondence**: Verified incrementally across three layers:
   - `make binary` verifies C ABI struct layouts via `_Static_assert` (`sizeof` plus per-field `offsetof`/`sizeof` across **10** ABI structs / **163** fields: `struct z_stream_s`, `struct gz_header_s`, `ct_data`, `static_tree_desc`, `tree_desc`, `deflate_state`, `code`, `struct inflate_state`, `struct gzFile_s`, and `gz_state`), emits standalone units via the Zlib-agnostic compiler ([Simple.lean](../Lean2C/Simple.lean), [ABI.lean](../Lean2C/ABI.lean), [Archive.lean](../Lean2C/Archive.lean)), compiles **5 / 15 standalone 100%-Lean units** (`adler32.c`, `compress.c`, `gzclose.c`, `uncompr.c`, `zutil.c`; **21** functions, with zero lines of original `.c`) directly to `.o`, splices Lean-generated headers (`3 / 3`) and **15** additional lowered functions (**36** Lean functions in `.o` total; **1** skipped variadic `gzprintf`, **123** unlowered) into the remaining **10** units, and checks byte-for-byte identity of all `15 / 15` `.o` object files and `build/libz.a` ([binary_audit.py](../tools/binary_audit.py)).
   - `make audit` compares normalized Clang JSON ASTs and target macros ([audit.py](../tools/audit.py)).
   - `make differential` runs all 10 fixed-seed test suites comparing compiled Lean executables against patched `libz.a` ([differential.py](../tools/differential.py)).

## 3. Manual Undefined-Behavior Exceptions

A no-fault theorem rules out `Fault.ub` as defined by the Lean runtime ([Ptr.lean](../ZlibF/Runtime/Ptr.lean)). Two C17 pointer-arithmetic rules are deliberately given defined semantics in the Lean model (inherited from `oss-proof`); their behavior in compiled C therefore rests on target-compiler review outside the Lean guarantee.

### Accepted Exceptions

| Operation | Model rule & rationale | Where it matters in patched zlib |
| --- | --- | --- |
| `Ptr.add p 0` (incl. subtracting `0`) | Returns `(p, h)` without checking liveness, modeling a zero-byte cursor advance for any pointer value (including `NULL` or a pointer into a freed buffer). | `gzseek64` ([gzlib.c.lean](../ZlibF/Zlib/gzlib.c.lean)) and `gz_skip_have` ([gzread.c.lean](../ZlibF/Zlib/gzread.c.lean)) can execute `state->x.next += n` when `n == 0`, while `x.next` is unwritten or refers to an expired caller buffer. |
| `Ptr.diff .null .null` | Returns signed `0` and preserves the heap (matching C++ semantics), allowing byte-count computation into an empty output buffer. | `compress2_z` ([compress.c.lean](../ZlibF/Zlib/compress.c.lean), [Utilities.lean](../ZlibF/Spec/Common/Utilities.lean)) reaches `stream.next_out - dest` with both operands `NULL` when `*destLen == 0` and `dest == NULL`. |

Inspect the corresponding Lean lemmas `Ptr.add_zero` and `Ptr.diff_null_null` in [Ptr.lean](../ZlibF/Runtime/Ptr.lean), and run `make reference` to inspect `gzlib.c`, `gzread.c`, and `compress.c` under `build/reference/`.

### Other Null-Pointer & Initialization Cases

| Case | Semantics & safety interpretation | Reference |
| --- | --- | --- |
| Null access or invalid arithmetic | Dereferencing `NULL`, adding a nonzero offset to `NULL`, subtracting `NULL` from non-`NULL`, or subtracting pointers to distinct allocations all raise `Fault.ub` and are excluded by no-fault theorems. | [Ptr.lean](../ZlibF/Runtime/Ptr.lean) |
| Zero-length libc calls | Modeled `memcpy`, `memmove`, and `memset` fault on `NULL` pointers even when `n == 0`; `free(NULL)` is a defined no-op. | [Libc.lean](../ZlibF/Runtime/Libc.lean) |
| Null accepted by API | `crc32` accepts `NULL` initial-value queries at any length; `adler32` accepts `NULL` only at length `0`; `gzgetc(NULL)` is a proved refusal for the function, though the `gzgetc` macro dereferences the handle before calling the function. | [Checksums.lean](../ZlibF/Spec/Common/Checksums.lean), [GzRefusal.lean](../ZlibF/Spec/Safety/GzRefusal.lean) |
| Unwritten pointer fields | Fresh modeled struct records initialize pointer fields to `NULL`, whereas C leaves them indeterminate (`free` / comparisons on unwritten C pointers remain a source-review obligation). | [Schema.lean](../ZlibF/Runtime/Schema.lean) |

### Recording a New Exception

Any newly proposed UB exception must document: (1) exact operand conditions and C17 rule, (2) exact expression in patched zlib and corresponding Lean primitive, (3) chosen model result and heap effect, (4) rationale and affected safety goals, and (5) at least one adjacent case that must continue to raise `Fault.ub`. Keep new proposals open until reviewed and implemented explicitly in the runtime.
