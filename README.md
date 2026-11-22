# zlib-lean

**Formal memory- and execution-safety verification of patched zlib (`1.4.0.1-motley`) in Lean 4.**

`zlib-lean` verifies memory safety, bounds safety, allocation ownership, disjoint multi-stream interleaving, and termination properties for all **86** documented public functions of patched zlib (`617e19a` + 6 patches in [pins.json](pins.json)) targeting the default x86-64 Linux LP64 static build, alongside an experimental Lean-to-C compiler (`Lean2C`) with formal C99 lowering soundness proofs for lowered kernels.

## Using the Safety Theorems

[`ZlibF.Results.whole_library_safety`](ZlibF/Results.lean) provides the preserved baseline contract for every documented `zlib.h` function (`PublicEntry`) and for the four stateful single-object protocols (`deflate`, `inflate`, `inflateBack`, and `gzip` via `StreamProtocol`). [`ZlibF.Results.extended_library_safety`](ZlibF/Results.lean) composes `whole_library_safety` with pointer-cell C-ABI companion contracts (`CAbiCompanion`: `compress*_c`) and sequential disjoint multi-stream interleaving contracts (`MultiStreamContract`):

```lean
import ZlibF.Results

open ZlibF.Results ZlibF.Spec.Public

example : Goal.compressBound_z := whole_library_safety.1 .compressBound_z
example : Goal.inflateCopy_safety := whole_library_safety.1 .inflateCopy
example : Goal.gz_sequence_safety := whole_library_safety.2 .gzip

example : Goal.compress2_c_safety := extended_library_safety.2.1 .compress2_c
example : Goal.multi_stream_step_safety := extended_library_safety.2.2 .stepSafety
```

See [ZlibF/Spec/Safety/WholeLibrary.lean](ZlibF/Spec/Safety/WholeLibrary.lean) for the selector definitions, [tests/public-api.json](tests/public-api.json) for the per-API mapping from C functions to Lean goals, and [docs/SAFETY.md](docs/SAFETY.md) for a C-auditor walkthrough of the safety predicates.

## What Is Verified (and What Is Not)

```mermaid
flowchart LR
    Model["Lean 4 Model & Runtime\n(ZlibF/Zlib, Runtime)"] --> Safety["Safety Proofs\n(134 proved / 0 remaining / 109 required)"]
    Safety --> Kernel["leanchecker --fresh\n(ZlibF.Results)"]
    Safety --> Coverage["make library-safety\n(zlib.h + baseline equiv check)"]
    Model --> Diff["make differential\n(Model vs patched C libz.a)"]
    Model -. "5/15 units lowered" .-> Lean2C["Lean2C & C99 Soundness\n(Semantics + Soundness proofs)"]
```

- **Formally proved in Lean 4**: All **134** safety goals in [ZlibF/Results.lean](ZlibF/Results.lean) are proved (**0** unproved, **109** required, including `whole_library_safety` and `extended_library_safety`), replayed in a fresh kernel with `leanchecker --fresh`, checked to depend only on `propext`, `Classical.choice`, and `Quot.sound`, matched against patched `zlib.h`, and checked for baseline spec/registry preservation against `85cd20c` ([check_baseline_equiv.py](tools/check_baseline_equiv.py), [LemmaEquivalence.lean](tests/LemmaEquivalence.lean)).
- **Formal C99 AST semantics & soundness for lowered kernels**: [Lean2C/Semantics.lean](Lean2C/Semantics.lean) and [Lean2C/Soundness.lean](Lean2C/Soundness.lean) (tested in [CSourceSoundness.lean](tests/CSourceSoundness.lean)) prove C99 §6.5.7 shift UB-freedom, load/store and loop simulation, and end-to-end `runCFn` soundness for the live lowered C ASTs of `compressBound_z`, `compressBound`, `zlibCompileFlags`, `byte_swap`, and `adler32_combine_`.
- **Executable model differential checks**: Fixed-seed test suites compare executables compiled from the Lean model against patched C `libz.a` across the default Linux LP64 configuration (`make differential`).
- **Remaining Lean-to-C gap (no full binary/AST equivalence claimed)**: [Lean2C](Lean2C/Simple.lean) compiles **5 / 15** standalone C units (`adler32.c`, `compress.c`, `gzclose.c`, `uncompr.c`, `zutil.c`), generates **3** header files (`crc32.h`, `inffixed.h`, `trees.h`), and checks C ABI struct layouts via `_Static_assert` for **10** core structs (**163** fields). C text rendering (`renderBody`/`renderStmts` in [Lean2C/C.lean](Lean2C/C.lean)), downstream `clang` compilation, and the remaining **10 / 15** unlowered units remain outside the formal compiler theorem.

For assumptions, C undefined-behavior boundaries, and the C-auditor walkthrough, see [docs/SAFETY.md](docs/SAFETY.md). For runtime, proof, and compiler module layout, see [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md).

## Commands

Requires Git, Python 3.9+, Make, Clang, and the Lean toolchain specified in [lean-toolchain](lean-toolchain).

```sh
git clone --recurse-submodules https://github.com/cla7aye15I4nd/zlib-lean
cd zlib-lean
make library-safety && make test
```

| Command | Purpose |
| --- | --- |
| `make library-safety` | Build `ZlibF` with `--wfail`, replay `ZlibF.Results` via `leanchecker --fresh`, verify all 86 public APIs against patched `zlib.h` ([check_public_safety.py](tools/check_public_safety.py)), and verify baseline equivalence against `85cd20c` ([check_baseline_equiv.py](tools/check_baseline_equiv.py)). |
| `make proof` | Build `ZlibF` with `--wfail` and replay `ZlibF.Results` in a fresh Lean kernel (~10 GB RAM). |
| `make test` | Build `Lean2C.Lower`, `Lean2C.Soundness`, `ZlibF.Proof.LibcMemory`, and `ZlibF.Proof.LibcScalar` with `--wfail`, run Lean tests with `-DwarningAsError=true` ([ShiftLowering.lean](tests/ShiftLowering.lean), [SafetyRules.lean](tests/SafetyRules.lean), [LemmaEquivalence.lean](tests/LemmaEquivalence.lean), [CSourceSoundness.lean](tests/CSourceSoundness.lean)), and run Python unit tests ([test_public_safety.py](tests/test_public_safety.py), [test_baseline_equiv.py](tests/test_baseline_equiv.py), [test_fidelity.py](tests/test_fidelity.py)). |
| `make differential` | Build patched C `libz.a` and Lean drivers, then compare outputs across 10 fixed-seed test suites ([tests/list.txt](tests/list.txt); full Linux parity targets x86-64 LP64). |
| `make binary` | Diagnostic C compilation check: verify `_Static_assert` ABI layouts across 10 structs, compile generated standalone units and spliced C units, and emit `build/binary-report.json`. |
| `make reference` | Reconstruct the 26-file patched C baseline in `build/reference/` from [upstream/](upstream) and [patches/](patches). |

## Provenance & License

Derived from [oss-proof](https://github.com/cla7aye15I4nd/oss-proof/blob/0784b3e17eb85bb7699f55cb975ed1d47c1452dc/projects/zlib/README.md) at commit `0784b3e` and focused on the safety verification closure. Upstream zlib source pins and patch SHA-256 digests are recorded in [pins.json](pins.json); modified zlib sources retain [patches/ZLIB-LICENSE](patches/ZLIB-LICENSE).
