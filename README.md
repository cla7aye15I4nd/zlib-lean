# zlib-lean

This fork's verification scope is **safety**. The Lean 4 model covers the 86 documented public functions of zlib 1.4.0.1-motley at `617e19a`, with six patches, for the default x86-64 Linux LP64 static build. For calls that meet their preconditions, the safety goals describe which faults are excluded, where a call may write, which allocations it may keep or release, and when it returns. Malformed compressed data is within scope when the caller supplies valid buffers. [Safety claim and assumptions](docs/en/trusted-base.md)

Some C operations have deliberately more permissive semantics in the model. For example, subtracting two null pointers yields zero there. A load through a null pointer still faults. The exception register names the precise operations, where the patched source uses them, and what that means for a claim about C. [Undefined-behavior exceptions](docs/en/model-limits.md)

Run `make proof` to check the Lean registry. It still includes functional results inherited from oss-proof, including the default-stream round trip. Those results are outside this fork's verification scope. [Local registry](ZlibF/Results.lean) · [Original oss-proof scope](https://github.com/cla7aye15I4nd/oss-proof/blob/0784b3e17eb85bb7699f55cb975ed1d47c1452dc/projects/zlib/README.md)

## Lean-to-C comparison

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
| `CLANG=clang-18 make audit-pinned` | Run the CI comparison on Ubuntu 24.04 x86-64. The audit checks the compiler build in `pins.json` and gives both configure and Clang the same Linux target and GNU C17 dialect. |
| `make emit` | Emit C for every module in `ZlibF/Zlib` and `ZlibF/Runtime`, plus three source-format headers, into `build/generated/`. |
| `make reference` | Reconstruct the independent 26-file C and header baseline in `build/reference/` from immutable Git blobs and the ordered patch series. |
| `make bytes` | Compare the two directory trees byte for byte, including comments, whitespace, inactive branches, extra files, and missing files. Save the first differing byte per file in `build/bytes.json`. |
| `make differential` | Build patched zlib and the native Lean drivers. Run all ten fixed-seed test suites and compare each line of output. |
| `make proof` | Build the proof registry with warnings as errors, then replay it in a fresh kernel environment. The replay needs about 10 GB of memory. |
| `make test` | Run the AST, byte-comparison, and coverage regression tests after `make audit`. |

To compare two C files directly, supply the include directories and defines their build requires. The comparator returns 0 for equal ASTs and a nonzero status for a difference or parse error.

```sh
python3 tools/ast_compare.py expected.c generated.c -- -Iinclude -DFEATURE=1
python3 tools/ast_compare.py --function byte_swap expected.c generated.c -- --target=x86_64-unknown-linux-gnu -std=gnu17 -Iinclude
```

The default comparison includes the whole translation unit. `--function` selects a main-file definition and follows declaration references, redeclarations and names in type spellings. This keeps a referenced inline helper and the fields of a referenced structure in scope, while an unrelated header typedef can be skipped. Both sides need headers for the selected target. The comparison measures structural equality of the information Clang exports in JSON. For example, Clang can dump `offsetof(struct S, x)` and `offsetof(struct S, y)` identically. The checker reports this node, inline assembly and pragma-specified field alignment as unsupported when they enter the comparison.

## What each result compares

* **Native C.** The Lean tool requests the pinned compiler's C backend for all 22 implementation modules and 10 runtime modules. It takes no reference C input. The generated units use Lean objects, runtime operations, and compiler-generated declarations. A missing original declaration is sufficient evidence of a different translation-unit AST.
* **Source-format function bodies.** A second pass walks elaborated Lean expressions and renders supported calls and arguments as C. The checker places a generated body into the original declaration context so both use the same parameter types, prototypes, and macros. Only the replaced body receives a comparison result. An unsupported expression or invalid candidate is reported explicitly. Original C bodies and Lean comments are never used to fill a missing translation. [Lean source emitter](Lean2C/Forward.lean)
* **Macros and comments.** Clang preprocesses both inputs with the same compiler flags. Comments, source coordinates, compiler allocation IDs, and redundant expression parentheses are discarded. Operators, operands, types, casts, bindings, statement order, and literal values are retained. The audit also compares 15 numeric settings with constants evaluated from the Lean model. For example, the target CRC configuration selects `W=4`, `N=5`, `NLOW=2`, and `BRAID_CUT=320`. A macro and its expansion can therefore match. An inactive branch needs a separate build configuration to exercise it.
* **Generated headers.** Lean renders `inffixed.h`, `trees.h`, and `crc32.h` from model tables with independently implemented printers. Declaration spelling, comment text, and line layout are explicit printer metadata. CRC braid tables for configurations absent from the model are calculated from the model's byte table. All three complete headers match the patched reference byte for byte, including the inactive CRC branches. [Header emitters](Lean2C/Headers.lean)
* **Behavior.** Differential results compare the patched C with executables compiled from the Lean definitions used in the proofs. Equal outputs establish agreement on the tested inputs. Applying a safety theorem to C also depends on the accuracy of the translation and the runtime model. [Trusted base](docs/en/trusted-base.md)

### Binding and arithmetic checks

The checker numbers parameters and local variables by declaration order. Every use retains its resolved binding, including uses in nested scopes. Function and field names and block-scope externs retain their spellings. For a VLA bound such as `int a[n]`, Clang may export only the text of the bound. The checker conservatively keeps the original local names in that function. For source-format bodies, the audit puts the emitter's parameter names into the original signature by position and checks the resulting declaration and body together.

The unsigned shift emitter keeps a raw C shift for an in-range literal, a bounded mask or remainder, or a count bounded by a recognized enclosing unsigned comparison. Otherwise it emits the Lean count modulo 8, 16, 32 or 64. For example, an unguarded `UInt64` right shift emits `x >> (n % 64)`. Its count has a different AST from the C expression `x >> n`. For narrow unsigned products the emitter widens to unsigned arithmetic before narrowing the result. The comparator retains each `ImplicitCastExpr`, including the promotion to signed `int` in a C product of two `unsigned short` operands. These results describe emitted syntax. Transferring a safety goal also requires the C operation to be defined on the theorem's input domain and the memory accesses to satisfy its caller premises. [Source lowering](Lean2C/Lower.lean) · [Caller memory contracts](ZlibF/Spec/Common/Memory.lean)

## Provenance

The original `ZlibF/` import came from oss-proof commit `0784b3e17eb85bb7699f55cb975ed1d47c1452dc`. The imported Git tree object was `94fa7f04ca73c042a4fe8f8cb6b4fe9486374263`. The [pins](pins.json) also identify the zlib source commit and the SHA-256 digest of each patch. zlib and its modified sources retain the [upstream license](patches/ZLIB-LICENSE).

This branch layers the libc runtime and pilots Hoare triples on the CRC word reader. The migration plan records the proof-size comparison and the axiom checks. [试点与迁移计划](docs/zh/proof-modernization.md)
