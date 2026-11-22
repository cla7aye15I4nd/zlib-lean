# Repository Architecture

`zlib-lean` separates the Lean 4 model of zlib, the runtime/libc semantics, the formal safety proofs, and the experimental Lean-to-C compiler (`Lean2C`) into independent layers.

## 1. Directory Layout

| Path | Responsibility |
| --- | --- |
| `ZlibF/Runtime/` | Memory model (`Space`, `Ptr`, `Monad`, `Schema`, `Tables`, `Address`), split C library models (`LibcMemory`, `LibcAllocation`, `LibcCString`, `LibcTables`, `Libc`), and C ABI type annotations (`CAbi`). |
| `ZlibF/Zlib/` | Lean 4 translations of the 15 zlib translation units, internal headers (`crc32.h`, `inffixed.h`, `trees.h`, `gzguts.h`, `zlib.h`), and the POSIX `gz*` I/O model (`gzfs.lean`). |
| `ZlibF/Spec/` | Common invariants (`Spec/Common/`), retained bound/query specifications (`Spec/Functional/Queries.lean`), public safety goals (`Spec/Safety/`), and the whole-library contract selectors (`Spec/Safety/WholeLibrary.lean`). |
| `ZlibF/Proof/` | Reusable Hoare/frame/loop combinators (`HeapWP`, `CountedLoop`, `LibcArray`, `LibcMemory`), per-module safety proofs, and public sequence/refusal/domain theorems. |
| `ZlibF/Results.lean` | Safety goal registry, `whole_library_safety` assembly, and `#eval checkWith` completeness check ([ResultsCheck.lean](../ZlibF/ResultsCheck.lean)). |
| `Lean2C/` | Standalone Lean-to-C compiler ([Simple.lean](../Lean2C/Simple.lean), [ABI.lean](../Lean2C/ABI.lean), [Archive.lean](../Lean2C/Archive.lean)), table header generators ([Headers.lean](../Lean2C/Headers.lean)), and diagnostic C lowerers. |
| `tools/` & `tests/` | Public API coverage verification (`check_public_safety.py`), differential test runner (`differential.py`), source/ABI compilation diagnostics (`binary_audit.py`, `audit.py`), and regression tests. |

## 2. Runtime & LibC Model

- **Heap and pointers**: [`Space.lean`](../ZlibF/Runtime/Space.lean), [`Monad.lean`](../ZlibF/Runtime/Monad.lean), and [`Ptr.lean`](../ZlibF/Runtime/Ptr.lean) define the computation monad `C.M` (`StateT Heap (Except Fault)`) and checked pointer operations (`Ptr.add`, `Ptr.load`, `Ptr.index`, `Ptr.store`, `Ptr.diff`, `Ptr.lt`).
- **Modular C library semantics**: [`Libc.lean`](../ZlibF/Runtime/Libc.lean) re-exports four focused modules (alongside [`Alloc.lean`](../ZlibF/Runtime/Alloc.lean) for backward-compatible imports):
  - [`LibcMemory.lean`](../ZlibF/Runtime/LibcMemory.lean): `Ptr.memcpy`, `Ptr.memmove`, `Ptr.fill`, `Ptr.memset`, `memcpyB`, `memmoveB`, `memsetB`, and byte-repeat instances.
  - [`LibcAllocation.lean`](../ZlibF/Runtime/LibcAllocation.lean): byte/word/struct block allocation and `free` (`allocB`, `freeB`, `allocK`, `freeK`), oracle-driven allocation failure, and `PTRDIFF_MAX` guards.
  - [`LibcCString.lean`](../ZlibF/Runtime/LibcCString.lean): `strlenB` and read-only string literal tables (`strLitRef`).
  - [`LibcTables.lean`](../ZlibF/Runtime/LibcTables.lean): whole-record `copyK` / `zeroK` operations on modeled zlib structs.
- **File system & C ABI surface**: [`gzfs.lean`](../ZlibF/Zlib/gzfs.lean) models file descriptors, buffered reads/writes, `lseek`, `fcntl`, `snprintf`, and `errno`. [`CAbi.lean`](../ZlibF/Runtime/CAbi.lean) provides zero-overhead `[reducible]` / `abbrev` wrappers (`CExport`, `CStatic`, `CHidden`, `COrder`, `ZOffT`, `ZOff64T`, `ZWordT`, `ZCrcT`, pointer qualifiers, out-parameters, and stack storage markers) so C ABI metadata lives in Lean function types without changing safety proofs.

## 3. Proof Architecture

- **Weakest-precondition interface ([HeapWP.lean](../ZlibF/Proof/HeapWP.lean))**: `open scoped C.HeapWP` equips `StateT Heap (Except Fault)` for `Std.WP` reasoning and connects fault-free `OkOn` obligations to Hoare triples (`okOn_iff_triple`, `Ptr.index_spec`).
- **Frame rules ([Proof/LibcMemory.lean](../ZlibF/Proof/LibcMemory.lean), [LibcArray.lean](../ZlibF/Proof/LibcArray.lean))**: Reusable contracts such as `memcpyB_frame` and `memcpyB_range_frame` preserve arbitrary predicates on untouched blocks and array slices across copies (used in `inflateCopy` window proofs and byte-view reasoning).
- **Counted loops ([CountedLoop.lean](../ZlibF/Proof/CountedLoop.lean))**: `cwhile_steps_spec` packages strict iteration-count fuel bounds and loop-exit conditions into reusable loop contracts (used in `crc32` byte/word loops).
- **Whole-library closure ([WholeLibrary.lean](../ZlibF/Spec/Safety/WholeLibrary.lean), [Results.lean](../ZlibF/Results.lean))**: Every safety goal and witness theorem is registered in `ZlibF/Results.lean` and combined into `ZlibF.Results.whole_library_safety`, which quantifies over `PublicEntry` (all **86** documented `zlib.h` functions) and `StreamProtocol` (`deflate`, `inflate`, `inflateBack`, `gzip`).

## 4. Lean-to-C Compiler (`Lean2C`)

`Lean2C` is currently a work in progress toward self-contained C compilation from Lean:

- **Zlib-agnostic `MetaM` C compiler ([Simple.lean](../Lean2C/Simple.lean), [ABI.lean](../Lean2C/ABI.lean), [Archive.lean](../Lean2C/Archive.lean))**: Inspects Lean expressions and `CAbi` type wrappers to emit C99 functions, structs, static tables, and C ABI struct definitions without hardcoding zlib-specific function names.
- **Header emitters ([Headers.lean](../Lean2C/Headers.lean))**: Renders `crc32.h`, `inffixed.h`, and `trees.h` directly from Lean model tables.
- **Current coverage & gaps**: Today, **5 / 15** zlib units (`adler32.c`, `compress.c`, `gzclose.c`, `uncompr.c`, `zutil.c`) emit standalone compilable C, **3 / 3** table headers match reference bytes, and **10** core ABI structs (**163** fields) pass `_Static_assert` size/offset verification. The remaining **10 / 15** C translation units rely heavily on `goto`-heavy state machines, complex preprocessor macros, or C variadics (`gzprintf`), and are not yet independently lowered from Lean. End-to-end binary equivalence or AST equivalence is therefore **not** claimed.

## 5. Local Verification

- **Safety proofs & API coverage**: `make library-safety` (requires `upstream` submodule initialized via `git submodule update --init upstream`) builds `ZlibF` with `--wfail`, replays `ZlibF.Results` via `leanchecker --fresh`, and runs [check_public_safety.py](../tools/check_public_safety.py).
- **Regression tests**: `make test` builds `Lean2C.Lower` and `ZlibF.Proof.LibcMemory`, executes [tests/ShiftLowering.lean](../tests/ShiftLowering.lean) and [tests/SafetyRules.lean](../tests/SafetyRules.lean), and runs the Python regression tests in `tests/`.
- **Differential testing**: `make differential` compiles the Lean model and patched C `libz.a` on fixed-seed inputs ([tools/differential.py](../tools/differential.py)). Because the Lean model hardcodes `C.OS_CODE = 3` for Linux LP64 whereas Apple hosts preprocess `OS_CODE = 19` in patched `zutil.h`, running `gz` and `deflate` differential suites to full parity requires a Linux x86-64 LP64 environment (`CC=/usr/bin/clang-18` on Ubuntu `24.04`).
- **Diagnostic C compilation check**: `make binary` runs [binary_audit.py](../tools/binary_audit.py) to compile generated standalone C, check `_Static_assert` ABI layouts, and inspect output object files under `build/`.
