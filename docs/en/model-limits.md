# Manual exceptions for undefined behavior

A no-fault theorem uses the operations defined by the Lean runtime. This fork accepts the two pointer-arithmetic rules below for its pinned target. Both were already present in oss-proof. C17 pointer arithmetic requires an appropriate array object or one-past pointer. Two null pointer **values** satisfy neither condition. Giving the expressions a result in Lean leaves their behavior in compiled C outside the guarantee. [Runtime definitions](../../ZlibF/Runtime/Ptr.lean) · [Pinned upstream analysis](https://github.com/cla7aye15I4nd/oss-proof/blob/0784b3e17eb85bb7699f55cb975ed1d47c1452dc/projects/zlib/docs/en/spec/safety.md#null-pointers-and-pointer-differences)

## Accepted exceptions

| Operation | Decision and rationale | Where it matters |
| --- | --- | --- |
| Add a zero offset to a pointer (`Ptr.add p 0`, including subtracting an integer zero) | Return the same pointer and heap without checking liveness. This models advancing a buffer cursor by zero bytes. The rule applies to every represented pointer, including null and a pointer into a freed buffer. | `gzseek64` and `gz_skip_have` can execute `state->x.next += n` with `n == 0`. The field can be unwritten or still refer to a caller buffer whose lifetime has ended. The proofs tolerate that arithmetic. [Seek translation](../../ZlibF/Zlib/gzlib.c.lean) · [Read translation](../../ZlibF/Zlib/gzread.c.lean) |
| Subtract two null pointer values (`Ptr.diff .null .null`) | Return signed zero and preserve the heap. This lets the model count bytes produced into an empty destination. | A `compress` call with a valid length cell holding zero and a null destination can reach `stream.next_out - dest` in `compress2_z` after initialization succeeds. Both pointer values are then null. [Compression translation](../../ZlibF/Zlib/compress.c.lean) · [Safety contract](../../ZlibF/Spec/Common/Utilities.lean) |

To inspect the matching C expressions, run `make reference` and open `gzlib.c` (`gzseek64`), `gzread.c` (`gz_skip_have`) and `compress.c` (`compress2_z`) under `build/reference/`. On the Lean side, the lemmas `Ptr.add_zero` and `Ptr.diff_null_null` state the result of each operation exactly. Both leave the heap untouched. A subsequent dereference still checks that its target is live and in bounds. [Pointer primitives and lemmas](../../ZlibF/Runtime/Ptr.lean)

## Other null-pointer cases

| Case | How to read the safety result |
| --- | --- |
| Null access or invalid arithmetic | A null load or store, a nonzero offset on null, and a difference between a null and a non-null pointer all raise `Fault.ub`. Subtracting pointers into distinct allocations also faults. A no-fault goal excludes these operations on its domain. [Pointer checks](../../ZlibF/Runtime/Ptr.lean) |
| Zero-length libc call | The modeled `memcpy` and `memmove` fault if either pointer is null, even at length zero. The modeled `memset` faults on a null destination at length zero. `free(NULL)` is an ordinary defined no-op. [Memory operations](../../ZlibF/Runtime/LibcMemory.lean) · [Allocation and free](../../ZlibF/Runtime/LibcAllocation.lean) |
| Null accepted by an API | The CRC buffer contract admits a null initial-value query for any length. The Adler buffer contract admits null only at length zero. A null handle passed to the `gzgetc` **function** is a proved refusal. The `gzgetc` macro reads a handle field before it can call the function, so that refusal theorem cannot be applied to the macro on null. [Checksum domains](../../ZlibF/Spec/Common/Checksums.lean) · [Gzip refusals](../../ZlibF/Spec/Safety/GzRefusal.lean) |
| Unwritten pointer field | Fresh modeled records give pointer fields a null value. An unwritten C field can hold an indeterminate value. For example, a modeled comparison or free can succeed and hide a missing initialization in C. Treat initialization before use as an outstanding source-review obligation wherever the C claim relies on it. [Record initializers](../../ZlibF/Runtime/Schema.lean) · [Upstream model limits](https://github.com/cla7aye15I4nd/oss-proof/blob/0784b3e17eb85bb7699f55cb975ed1d47c1452dc/projects/zlib/docs/en/model-limits.md) |

## Recording a new decision

When reviewing a new case, identify the exact C expression in the patched source, the corresponding Lean primitive or theorem premise, and the inputs on which they differ. A premise excludes calls from a theorem's domain. An exception gives an operation a defined model result **inside** that domain. A representation gap can hide a fault and belongs in the trusted base until resolved.

For a proposed exception, record its operand conditions, the C rule, the chosen model result and heap effects, the reason for the choice, and the affected calls or goals. Give one adjacent case that must still fault. Mark the proposal as open until a maintainer accepts that specific rule and the runtime implements it. A passing proof or test cannot make that decision. Revisit the entry when a source patch, platform change, or runtime edit changes its premise or removes its use.
