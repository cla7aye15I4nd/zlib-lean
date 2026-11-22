# zlib-lean

This repository contains the Lean 4 proof for zlib and a Lean-to-C translator with a Clang AST comparison. The reference is zlib 1.4.0.1-motley at `617e19a` with the six patches in this repository, built as a default x86-64 Linux LP64 static library. The original proof covers the safety of 86 documented public functions under their stated preconditions, together with the round trip of the default zlib stream. [Proof scope](https://github.com/cla7aye15I4nd/oss-proof/blob/0784b3e17eb85bb7699f55cb975ed1d47c1452dc/projects/zlib/README.md) · [Trusted base](https://www.dataisland.org/oss-proof/zlib/en/trusted-base.html)

**The generated program and the reference have different C ASTs.** Lean compiles the executable heap model to C with the Lean runtime ABI. A second emitter recovers source-level expressions from elaborated Lean definitions. The audit records which recovered function bodies have the same AST as their C originals, which differ, and which the source-level emitter cannot yet express. For example, the original `compressBound` declares a local and checks a conversion. Its Lean definition directly calls `compressBound_z`. The audit reports the differing statement nodes.

## Run the comparison

Use Git, Python 3.9 or later, Make, Clang, and the Lean version in `lean-toolchain` (available through elan). The GitHub Actions audit uses Ubuntu 24.04 x86-64. A local run on another platform selects that platform's C branches.

```sh
git clone --recurse-submodules https://github.com/cla7aye15I4nd/zlib-lean
cd zlib-lean
make audit
```

Read `build/ast-report.json` for each translation unit, active C function body, and library header, along with the Clang version and flags. All 86 documented functions are located independently in both the reference and the native output. Each entry records the compiler symbol and a concrete difference in its declaration. `make audit` succeeds when it produces the report and finds every documented API. **Use `make ast-equal` as the strict gate**. It exits unsuccessfully whenever a translation unit differs or a required source comparison is missing. The current revision is expected to fail that gate.

| Command | Result |
| --- | --- |
| `make emit` | Emit C for every module in `ZlibF/Zlib` and `ZlibF/Runtime`, plus three source-format headers, into `build/generated/`. |
| `make reference` | Reconstruct the independent 26-file C and header baseline in `build/reference/` from immutable Git blobs and the ordered patch series. |
| `make bytes` | Compare the two directory trees byte for byte, including comments, whitespace, inactive branches, extra files, and missing files. Save the first differing byte per file in `build/bytes.json`. |
| `make differential` | Build patched zlib and the native Lean drivers. Run all ten fixed-seed test suites and compare each line of output. |
| `make proof` | Build the proof registry with warnings as errors, then replay it in a fresh kernel environment. The replay needs about 10 GB of memory. |
| `make test` | Run the AST, byte-comparison, and coverage regression tests after `make audit`. |

To compare two C files directly, supply the include directories and defines their build requires. The comparator returns 0 for equal ASTs and a nonzero status for a difference or parse error.

```sh
python3 tools/ast_compare.py expected.c generated.c -- -Iinclude -DFEATURE=1
```

## What each result compares

* **Native C.** The Lean tool requests the pinned compiler's C backend for all 22 implementation modules and 10 runtime modules. It takes no reference C input. The generated units use Lean objects, runtime operations, and compiler-generated declarations. A missing original declaration is sufficient evidence of a different translation-unit AST.
* **Source-format function bodies.** A second pass walks elaborated Lean expressions and renders supported calls and arguments as C. The checker places a generated body into the original declaration context so both use the same parameter types, prototypes, and macros. Only the replaced body receives a comparison result. An unsupported expression or invalid candidate is reported explicitly. Original C bodies and Lean comments are never used to fill a missing translation. [Lean source emitter](Lean2C/Forward.lean)
* **Macros and comments.** Clang preprocesses both inputs with the same compiler flags. Comments, source coordinates, compiler allocation IDs, and redundant expression parentheses are discarded. Operators, operands, types, casts, bindings, statement order, and literal values are retained. The audit also compares 15 numeric settings with constants evaluated from the Lean model. For example, the target CRC configuration selects `W=4`, `N=5`, `NLOW=2`, and `BRAID_CUT=320`. A macro and its expansion can therefore match. An inactive branch needs a separate build configuration to exercise it.
* **Generated headers.** Lean renders `inffixed.h`, `trees.h`, and `crc32.h` from model tables with independently implemented printers. Declaration spelling, comment text, and line layout are explicit printer metadata. CRC braid tables for configurations absent from the model are calculated from the model's byte table. All three complete headers match the patched reference byte for byte, including the inactive CRC branches. [Header emitters](Lean2C/Headers.lean)
* **Behavior.** Differential results compare the real C with executables compiled from the same Lean definitions as the proofs. Equal outputs establish agreement on the tested inputs. The original safety and round-trip theorems have their own hypotheses and trusted base.

## Provenance

The entire `ZlibF/` tree is preserved from oss-proof commit `0784b3e17eb85bb7699f55cb975ed1d47c1452dc`. Its Git tree object is `94fa7f04ca73c042a4fe8f8cb6b4fe9486374263`. The [pins](pins.json) also identify the zlib source commit and the SHA-256 digest of each patch. zlib and its modified sources retain the [upstream license](patches/ZLIB-LICENSE).
