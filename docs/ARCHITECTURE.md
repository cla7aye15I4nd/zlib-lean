# Repository Architecture

`zlib-lean` separates the Lean 4 model of zlib, the runtime/libc semantics, the formal safety proofs, and the Lean-to-C compiler (`Lean2C`) and its formal soundness layer into independent layers.

## 1. Directory Layout

| Path | Responsibility |
| --- | --- |
| `ZlibF/Runtime/` | Memory model (`Space`, `Ptr`, `Monad`, `Schema`, `Tables`, `Address`), split C library models (`LibcMemory`, `LibcAllocation`, `LibcCString`, `LibcStrings`, `LibcTables`, `Libc`), and C ABI type annotations (`CAbi`). |
| `ZlibF/Zlib/` | Lean 4 translations of the 15 zlib translation units, internal headers (`crc32.h`, `inffixed.h`, `trees.h`, `gzguts.h`, `zlib.h`), and the POSIX `gz*` I/O model (`gzfs.lean`). |
| `ZlibF/Spec/` | Common invariants (`Spec/Common/`), retained bound/query specifications (`Spec/Functional/Queries.lean`), public safety goals (`Spec/Safety/`, including `UtilitiesCAbi.lean` and `MultiStream.lean`), and the whole-library contract selectors (`Spec/Safety/WholeLibrary.lean`). |
| `ZlibF/Proof/` | Reusable Hoare/frame/loop/scalar combinators (`HeapWP`, `CountedLoop`, `LibcArray`, `LibcMemory`, `LibcScalar`), per-module safety proofs, C-ABI companion proofs (`public-compress-safe-c.lean`), and disjoint multi-stream proofs (`public-multi-stream-safety.lean`). |
| `ZlibF/Results.lean` | Safety goal registry, `whole_library_safety` & `extended_library_safety` assembly, and `#eval checkWith` completeness check ([ResultsCheck.lean](../ZlibF/ResultsCheck.lean)). |
| `Lean2C/` | Standalone Lean-to-C compiler ([Simple.lean](../Lean2C/Simple.lean), [Lower.lean](../Lean2C/Lower.lean), [C.lean](../Lean2C/C.lean), [ABI.lean](../Lean2C/ABI.lean), [Archive.lean](../Lean2C/Archive.lean), [Headers.lean](../Lean2C/Headers.lean)) plus formal C99 LP64 operational semantics ([Semantics.lean](../Lean2C/Semantics.lean)) and lowering soundness proofs ([Soundness.lean](../Lean2C/Soundness.lean)). |
| `tools/` & `tests/` | Public API coverage verification (`check_public_safety.py`), baseline equivalence checker (`check_baseline_equiv.py`), differential test runner (`differential.py`), binary/AST checks (`binary_audit.py`, `audit.py`), and Lean/Python regression suites (`ShiftLowering.lean`, `SafetyRules.lean`, `LemmaEquivalence.lean`, `CSourceSoundness.lean`, `test_*.py`). |

## 2. Runtime & LibC Model

- **Heap and pointers**: [`Space.lean`](../ZlibF/Runtime/Space.lean), [`Monad.lean`](../ZlibF/Runtime/Monad.lean), and [`Ptr.lean`](../ZlibF/Runtime/Ptr.lean) define the computation monad `C.M` (`StateT Heap (Except Fault)`) and checked pointer operations (`Ptr.add`, `Ptr.load`, `Ptr.index`, `Ptr.store`, `Ptr.diff`, `Ptr.lt`).
- **Modular C library semantics**: [`Libc.lean`](../ZlibF/Runtime/Libc.lean) re-exports the split libc/table modules (alongside [`Alloc.lean`](../ZlibF/Runtime/Alloc.lean) for backward-compatible imports):
  - [`LibcMemory.lean`](../ZlibF/Runtime/LibcMemory.lean): `Ptr.memcpy`, `Ptr.memmove`, `Ptr.fill`, `Ptr.memset`, `memcpyB`, `memmoveB`, `memsetB`, and byte-repeat instances.
  - [`LibcAllocation.lean`](../ZlibF/Runtime/LibcAllocation.lean): byte/word/struct block allocation and `free` (`allocB`, `freeB`, `allocK`, `freeK`), oracle-driven allocation failure, and `PTRDIFF_MAX` guards.
  - [`LibcCString.lean`](../ZlibF/Runtime/LibcCString.lean) & [`LibcStrings.lean`](../ZlibF/Runtime/LibcStrings.lean): `strlenB`, string-array predicates, and read-only string literal tables (`strLitRef`).
  - [`LibcTables.lean`](../ZlibF/Runtime/LibcTables.lean): whole-record `copyK` / `zeroK` operations on modeled zlib structs.
- **File system & C ABI surface**: [`gzfs.lean`](../ZlibF/Zlib/gzfs.lean) models file descriptors, buffered reads/writes, `lseek`, `fcntl`, `snprintf`, and `errno`. [`CAbi.lean`](../ZlibF/Runtime/CAbi.lean) provides zero-overhead `[reducible]` / `abbrev` wrappers (`CExport`, `CStatic`, `CHidden`, `COrder`, `ZOffT`, `ZOff64T`, `ZWordT`, `ZCrcT`, pointer qualifiers, out-parameters, and stack storage markers) so C ABI metadata lives in Lean function types without changing safety proofs.

## 3. Proof Architecture

- **Weakest-precondition interface ([HeapWP.lean](../ZlibF/Proof/HeapWP.lean))**: `open scoped C.HeapWP` equips `StateT Heap (Except Fault)` for `Std.WP` reasoning and connects fault-free `OkOn` obligations to Hoare triples (`okOn_iff_triple`, `Ptr.index_spec`).
- **Frame rules ([Proof/LibcMemory.lean](../ZlibF/Proof/LibcMemory.lean), [LibcArray.lean](../ZlibF/Proof/LibcArray.lean), [LibcScalar.lean](../ZlibF/Proof/LibcScalar.lean))**:
  - `Proof/LibcMemory.lean`: reusable frame rules across byte copies and fills (`memcpyB_frame`, `memcpyB_range_frame`, `memmoveB_frame`, `memmoveB_range_frame`, `memsetB_frame`, `memsetB_range_frame`, `freeB_spec`, `freeB_frame`).
  - `LibcArray.lean`: array slice lemmas (`copyRange.succ`, `copyRange.getElem?`, `fillRange.succ`, `fillRange.getElem?`).
  - `LibcScalar.lean`: little-endian 32-bit/64-bit scalar memory contracts (`packLE32`/`packLE64`, `load32_spec`/`load64_spec`, `store32_frame`/`store64_frame`, `store32_load32_spec`/`store64_load64_spec`, and `bv_decide`-verified roundtrips).
- **Counted & invariant loops ([CountedLoop.lean](../ZlibF/Proof/CountedLoop.lean))**: `cwhile_steps_spec`, `cwhile_inv_spec`, `cdoWhile_steps_spec`, and `cdoWhile_inv_spec` package strict iteration-count fuel bounds and loop-exit invariants into reusable `Std.WP` contracts.
- **Whole-library & extended safety closure ([WholeLibrary.lean](../ZlibF/Spec/Safety/WholeLibrary.lean), [Results.lean](../ZlibF/Results.lean))**: All **134** safety goals (**0** unproved, **109** required) are registered in `ZlibF/Results.lean` and assembled into `ZlibF.Results.whole_library_safety` (`PublicEntry` for all **86** documented `zlib.h` functions + single-object `StreamProtocol`) and `ZlibF.Results.extended_library_safety` (`whole_library_safety` ∧ `CAbiCompanion` for `compress*_c` pointer-cell wrappers ∧ `MultiStreamContract` for disjoint multi-stream interleaving).

## 4. Lean-to-C Compiler (`Lean2C`) & Lowering Soundness

- **Zlib-agnostic `MetaM` C compiler ([Lower.lean](../Lean2C/Lower.lean), [C.lean](../Lean2C/C.lean), [Simple.lean](../Lean2C/Simple.lean), [ABI.lean](../Lean2C/ABI.lean), [Archive.lean](../Lean2C/Archive.lean))**: Extracts `Stmt` ASTs via `lowerStmts?`, renders C via `lower?` / `renderBody`, emits standalone C99 functions and structs from `CAbi` annotations, and verifies struct layouts against C via `_Static_assert`.
- **Header emitters ([Headers.lean](../Lean2C/Headers.lean))**: Renders `crc32.h`, `inffixed.h`, and `trees.h` directly from Lean model tables.
- **Formal C99 LP64 semantics & soundness ([Semantics.lean](../Lean2C/Semantics.lean), [Soundness.lean](../Lean2C/Soundness.lean))**: Models `evalValue`, `execStmt`, and `runCFn` on C99 `Stmt` trees, proving zero C99 §6.5.7 shift UB, load/store and loop simulation, and end-to-end `runCFn` soundness & `Goal.*` safety transfer for the lowered ASTs of `compressBound_z`, `compressBound`, `zlibCompileFlags`, `byte_swap`, and `adler32_combine_`.
- **Current coverage & gaps**: **5 / 15** zlib units (`adler32.c`, `compress.c`, `gzclose.c`, `uncompr.c`, `zutil.c`) emit standalone compilable C, **3 / 3** table headers match reference bytes, and **10** core ABI structs (**163** fields) pass `_Static_assert` size/offset verification. The remaining **10 / 15** C translation units rely on reference C splicing, and C pretty-printing (`renderStmts`) plus downstream `clang` compilation remain outside the kernel proof.

## 5. Local Verification

- **Safety proofs, API coverage & baseline equivalence**: `make library-safety` (requires `upstream` submodule initialized via `git submodule update --init upstream`) builds `ZlibF` with `--wfail`, replays `ZlibF.Results` via `leanchecker --fresh`, runs [check_public_safety.py](../tools/check_public_safety.py), and runs [check_baseline_equiv.py](../tools/check_baseline_equiv.py).
- **Regression tests**: `make test` builds `Lean2C.Lower`, `Lean2C.Soundness`, `ZlibF.Proof.LibcMemory`, and `ZlibF.Proof.LibcScalar` with `--wfail`, executes [tests/ShiftLowering.lean](../tests/ShiftLowering.lean), [tests/SafetyRules.lean](../tests/SafetyRules.lean), [tests/LemmaEquivalence.lean](../tests/LemmaEquivalence.lean), and [tests/CSourceSoundness.lean](../tests/CSourceSoundness.lean) with `-DwarningAsError=true`, and runs all Python unit tests (`test_*.py`, including [test_baseline_equiv.py](../tests/test_baseline_equiv.py)).
- **Differential testing**: `make differential` compiles the Lean model and patched C `libz.a` on fixed-seed inputs ([tools/differential.py](../tools/differential.py)). Because the Lean model hardcodes `C.OS_CODE = 3` for Linux LP64 whereas Apple hosts preprocess `OS_CODE = 19` in patched `zutil.h`, running `gz` and `deflate` differential suites to full parity requires a Linux x86-64 LP64 environment (`CC=/usr/bin/clang-18` on Ubuntu `24.04`).
- **Binary compilation check**: `make binary` runs [binary_audit.py](../tools/binary_audit.py) to compile generated standalone C, check `_Static_assert` ABI layouts, and verify object/archive parity under `build/`.
