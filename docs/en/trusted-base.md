# Safety claim and trusted base

The claim is about executions of the Lean translation of patched zlib. For example, `Goal.inflate_sequence_safety` starts with one reachable stream. For the next permitted call it establishes that the call returns, preserves the stream invariant, writes only the permitted regions, and accounts for every change to the set of live blocks. A stream can retain its window between calls. On a reachable inflate stream, `inflateEnd` frees the blocks the stream owns. A normal return can carry a zlib error code. [Stream sequence goals](../../ZlibF/Spec/Safety/Sequences.lean)

## Which calls are covered?

| Condition | Effect on the claim |
| --- | --- |
| Source and platform | The target is the pinned zlib revision with all six patches, built as a default x86-64 Linux LP64 static library. Where a goal requires `ByteObjectsFit`, the limit is fewer than `2^63` bytes **per byte object**. [Source and patches](../../pins.json) · [Platform predicate](../../ZlibF/Spec/Common/PlatformMemory.lean) |
| Allocation and caller memory | The goals cover the default allocator, including allocation failure. Custom allocators are outside scope. Each call specifies the extents, writability and separation required of its buffers. Two ranges can share an allocation when the relevant separation predicate allows disjoint intervals. [Memory predicates](../../ZlibF/Spec/Common/Memory.lean) |
| Stream history | Sequence goals follow one object from initialization or open. Between calls, the caller may replace buffers and change memory as permitted by the caller frame. Composing arbitrary histories across objects or threads is outside these goals. [Stream goals](../../ZlibF/Spec/Safety/Sequences.lean) · [Gzip handle history](../../ZlibF/Spec/Safety/GzSafety.lean) |
| Callback decoder | The `inflateBack` sequence goal requires returning callbacks that respect ownership and preserve the window. Its protocol bounds total input for one call to fewer than `2^48` bytes. [Callback sequence goal](../../ZlibF/Spec/Safety/Sequences.lean) |
| Gzip I/O | For `gzread`, `gzfread`, `gzgetc`, `gzgetc_`, `gzgets` and `gzungetc`, the goal excludes `Fault.ub` even without a read budget. For a general read on a reachable handle, a nonnegative descriptor with a read budget below `2^61` bytes guarantees return. Null-handle refusals and the buffered-output branch of the `gzgetc` macro return without this budget. Writes assume a nonempty OS write either fails or makes progress. [Gzip safety contract](../../ZlibF/Proof/gz.inv-model.lean) · [Read budget](../../ZlibF/Spec/Common/GzInv.lean) |
| Formatted output | For `gzprintf` and `gzvprintf`, the C caller must supply a defined format/argument combination without `%n`. The external formatter model bounds its writes and takes the result from its environment. It cannot detect a type mismatch in the caller's format. [Formatter model](../../ZlibF/Zlib/gzfs.lean) |

To trace one of the 86 functions, find its `safety_goal` in the API inventory, read the goal and its premises, then look up its theorem in `proved`. For example, `Goal.crc32_safety` gives a normal return and an unchanged heap. Its result value is existential. The two pure bound queries, `compressBound` and `compressBound_z`, use their stronger inherited contracts as their registry entries. [API inventory](../../tests/public-api.json) · [Checksum goals](../../ZlibF/Spec/Safety/Checksums.lean) · [Registry](../../ZlibF/Results.lean)

## Using the whole-library theorem

Import the registry to use the kernel-checked proof. The selector determines the proposition at the type level, so either projection recovers the existing contract with all of its premises. The protocol projection covers reachable histories of a single stream or handle under that protocol. [Selectors](../../ZlibF/Spec/Safety/WholeLibrary.lean) · [Proof and registration](../../ZlibF/Results.lean)

```lean
import ZlibF.Results

open ZlibF.Results ZlibF.Spec.Public

example : Goal.compressBound_z := whole_library_safety.1 .compressBound_z
example : Goal.inflateCopy_safety := whole_library_safety.1 .inflateCopy
example : Goal.gz_sequence_safety := whole_library_safety.2 .gzip
```

`make library-safety` also checks the documented declarations in the reconstructed header, the entries in the API inventory, the elaborated dispatcher and the selectors against the compiled registry. The header lists ten additional functions below its undocumented boundary. The registry separately requires `gzvprintf_safety`. [Coverage check](../../tools/check_public_safety.py) · [Public inventory](../../tests/public-api.json)

## From a Lean theorem to a claim about C

`make proof` builds with warnings treated as errors and replays `ZlibF.Results` in a fresh kernel environment. The registry checker verifies each registered theorem's type against its goal, requires a proof for every entry in `required`, and permits only `propext`, `Classical.choice` and `Quot.sound` as axioms. The inherited registry also requires functional theorems. Functional correctness, including round-trip correctness, is outside the scope maintained by this fork. [Build target](../../Makefile) · [Registry checker](../../ZlibF/ResultsCheck.lean)

Applying a theorem to C requires a faithful hand translation, an adequate model of the heap, libc and OS, and a goal that states the intended contract. For example, the CRC translation assembles a word from four byte reads. It proves facts about those reads while leaving the aliasing rules for the C word-pointer cast to source review. Compiler and hardware behavior are also outside the kernel check. The Clang audit compares syntax and the differential tests exercise selected executions. [CRC translation](../../ZlibF/Zlib/crc32.c.lean) · [Comparison commands](../../README.md#run-the-comparison)

For the pointer operations this fork deliberately treats as exceptions, consult the local register. For other per-function premises and representation limits, consult the pinned upstream documentation alongside the local Lean definition. [Local exceptions](model-limits.md) · [Upstream caller premises](https://github.com/cla7aye15I4nd/oss-proof/blob/0784b3e17eb85bb7699f55cb975ed1d47c1452dc/projects/zlib/docs/en/deviations.md) · [Upstream trusted base](https://github.com/cla7aye15I4nd/oss-proof/blob/0784b3e17eb85bb7699f55cb975ed1d47c1452dc/projects/zlib/docs/en/trusted-base.md)
