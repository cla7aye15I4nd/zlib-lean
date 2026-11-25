# Repository Architecture

`zlib-lean` is organized around a single-source-of-truth C99 representation: every zlib module is authored directly in a C-like Lean 4 macro DSL with Verus-style embedded function contracts, elaborated into one `C99.TU` AST consumed identically by the formal C99 small-step semantics and the 1-to-1 C printer.

## 1. Directory Layout & Size Summary

| Layer / Path | LOC | Responsibility |
| --- | ---: | --- |
| [`C99/`](../C99.lean) (Core TCB) | 2,179 | Zlib-agnostic LP64 C99 AST ([`AST.lean`](../C99/AST.lean), 406), flat byte-block memory ([`Mem.lean`](../C99/Mem.lean), 222), safety-only libc/POSIX ([`Libc.lean`](../C99/Libc.lean), 233), continuation semantics ([`Semantics.lean`](../C99/Semantics.lean), 978), 1-to-1 C printer ([`EmitC.lean`](../C99/EmitC.lean), 335), umbrella ([`C99.lean`](../C99.lean), 5). |
| [`C99/DSL/`](../C99/DSL.lean) | 1,618 | C99 grammar ([`Syntax.lean`](../C99/DSL/Syntax.lean)), unhygienic C preprocessor expander ([`Macro.lean`](../C99/DSL/Macro.lean)), scoped header/TU state ([`Env.lean`](../C99/DSL/Env.lean)), Verus contract record ([`Contract.lean`](../C99/DSL/Contract.lean), 22), fast elaborator ([`Elab.lean`](../C99/DSL/Elab.lean)), smoke test ([`Smoke.lean`](../C99/DSL/Smoke.lean)), umbrella ([`DSL.lean`](../C99/DSL.lean)). |
| [`Zlib/Headers/Common.lean`](../Zlib/Headers/Common.lean) & [`Zlib/Tables/`](../Zlib/Tables) | 1,612 | Shared ABI headers (`abi_common.h`, `abi_deflate.h`, `abi_inflate.h`, `abi_gz.h`), `c_spec_view Zlib.Spec.ClientView`, and static tables (`crc32.h`, `inffixed.h`, `trees.h`). |
| `Zlib/*.lean` (15 TUs + [`Zlib.lean`](../Zlib.lean)) | 6,780 | Human-readable C-like translations of all 15 zlib source files plus 86 Verus-style `c_fn` safety contracts. |
| [`Zlib/Spec/`](../Zlib/Spec/Safety.lean) | 316 | Safety-only memory/handle predicates ([`Memory.lean`](../Zlib/Spec/Memory.lean), 203) and whole-library safety goal [`Safety.lean`](../Zlib/Spec/Safety.lean) (113). |
| [`Main.lean`](../Main.lean) & [`scripts/verify.sh`](../scripts/verify.sh) | — | Unified Lean CLI (`emit`, `emit-abi-check`, `check-api`, `check-tcb`) and POSIX Clang/CompCert byte-equality verifier. |

## 2. Single-Source-of-Truth Pipeline

1. **C-like DSL & Verus Contract Elaboration ([`C99/DSL/`](../C99/DSL.lean))**:
   - `c_header_begin` .. `c_header_end` persists typedefs, struct/enum tags, constants, and preprocessor macros (`persistedScopeExt`) across module imports while emitting exact ABI header ASTs.
   - `c_tu_begin` .. `c_tu_end` elaborates C code with unhygienic macro expansion (`c_define`, `c_define_field`, `c_macro`, `c_stmt_macro`) into per-function helpers `{tu}_fn_{name} : C99.FnDef` and symbolic chunked `TU` lists for fast kernel compilation.
   - Optional Verus-style `requires ...;`, `modifies ...;`, and `ensures ...;` clauses directly on `c_fn` automatically unpack C parameters (`tags`, `owned`, `view`, `m`, C parameters / `vaArgs`, `ret`, `m'`, `view'`) into `def {name}_contract : C99.FnContract View` and collect `<tu>Contracts` at `c_tu_end`. All contract terms are completely erased from `C99.FnDef`, `C99.TU`, `C99.Semantics`, and `C99.EmitC`.

2. **Operational Semantics ([`C99/Semantics.lean`](../C99/Semantics.lean))**:
   - Evaluates `C99.AST` directly on LP64 x86-64 via deterministic step reduction (`stepDet`) plus nondeterministic relations (`Step`) for heap/stack/string allocation, OS/libc transitions (`C99.Libc.ExtStep`), and caller callbacks (`userExt`).
   - Parameterizes the two accepted C17 pointer-arithmetic rules explicitly through `PointerConfig`.

3. **Pure 1-to-1 C99 Emission ([`C99/EmitC.lean`](../C99/EmitC.lean)) & Byte-Identity Verification**:
   - `C99.EmitC` is a 335-LOC pure AST printer with zero metaprogramming or zlib knowledge.
   - [`Main.lean`](../Main.lean) (`lake exe lean2c`) emits all ABI headers (`abi_*.h`), table headers (`crc32.h`, `inffixed.h`, `trees.h`), all 15 `.c` units (`emit`), and direct AST-derived `_Static_assert` checks (`emit-abi-check`) verifying every size and field offset of all 10 ABI structs (163 fields).
   - [`scripts/verify.sh`](../scripts/verify.sh) materializes patched zlib (`build/reference/`), compiles both trees with identical Clang or CompCert flags, and asserts **15/15 byte-identical `.o` object files** and **byte-identical `libz.a`**, replacing differential test suites completely.
