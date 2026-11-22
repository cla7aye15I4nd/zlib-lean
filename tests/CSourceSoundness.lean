import Lean2C.Lower
import Lean2C.Soundness
import ZlibF.Results

/-!
# Verification that `Lean2C.Lower.lowerStmts?` matches `Lean2C.Soundness` ASTs

Checks against the live Lean environment that `Lean2C.Lower.lowerStmts?` produces the
exact parameter lists and statement ASTs verified by `Lean2C.Soundness`, and transfers
the registered `ZlibF` safety goals to the lowered C semantics (`runCFn`).
-/

deriving instance BEq for Lean2C.CSource.Stmt

namespace CSourceSoundnessTests
open Lean Elab Command
open Lean2C.CSource Lean2C.Semantics Lean2C.Soundness

run_cmd do
  let env ← getEnv
  let checks : List (Name × Bool × (List (String × Ty) × List Stmt)) :=
    [ (``Zlib.Compress.compressBound_z, false, compressBound_z_c)
    , (``Zlib.Compress.compressBound, true, compressBound_c)
    , (``Zlib.Zutil.zlibCompileFlags, true, zlibCompileFlags_c)
    , (``Zlib.Crc32.byte_swap, false, byte_swap_c)
    , (``Zlib.Adler32.adler32_combine_, true, adler32_combine_c)
    ]
  for (name, abi, expected) in checks do
    let some (.defnInfo d) := env.find? name
      | throwError "missing definition {name}"
    let some actual := Lean2C.Lower.lowerStmts? env name d.type d.value abi
      | throwError "lowerStmts? returned none for {name} (abi={abi})"
    unless actual == expected do
      throwError "lowerStmts? AST mismatch for {name} (abi={abi})"
    let some cText := Lean2C.Lower.lower? env name d.type d.value abi
      | throwError "lower? returned none for {name} (abi={abi})"
    if cText.isEmpty then
      throwError "lower? produced empty string for {name}"

/-- C-level `compressBound` contract instantiated from the registered Lean theorem. -/
theorem live_compressBound_c_spec
    (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (hfns : fns "compressBound_z" = some compressBound_z_c)
    (hfuel : 1 ≤ fuel) (sourceLen : UInt64) (h : C.Heap) :
    ∃ v, runCFn fns globals fuel compressBound_c [.u64 sourceLen] h = .ret (.u64 v) h ∧
      v.toNat = ZlibF.Spec.Api.compressBound sourceLen.toNat :=
  compressBound_c_spec fns globals fuel hfns hfuel ZlibF.Spec.Public.Proofs.compressBound sourceLen h

/-- C-level `zlibCompileFlags` safety instantiated from the registered Lean theorem. -/
theorem live_zlibCompileFlags_c_safety
    (fns : FnTable) (globals : CEnv) (fuel : Nat) (h : C.Heap) :
    ∃ flags, C.run Zlib.Zutil.zlibCompileFlags h = .ok (flags, h) ∧
      runCFn fns globals fuel zlibCompileFlags_c [] h = .ret (.u64 flags) h :=
  zlibCompileFlags_c_safety fns globals fuel
    ZlibF.Spec.Public.StatelessSafetyProof.zlibCompileFlags_safety h

/-- C-level `adler32_combine` safety instantiated from the registered Lean theorem. -/
theorem live_adler32_combine_c_safety
    (fns : FnTable) (fuel : Nat) (h : C.Heap) (adler1 adler2 : UInt64) (len2 : Int64) :
    ∃ res, C.run (Zlib.Adler32.adler32_combine adler1 adler2 len2) h = .ok (res, h) ∧
      runCFn fns defaultCGlobals fuel adler32_combine_c
        [.u64 adler1, .u64 adler2, .i64 len2] h = .ret (.u64 res) h :=
  adler32_combine_c_safety fns fuel
    ZlibF.Spec.Public.StatelessSafetyProof.adler32_combine_safety h adler1 adler2 len2

end CSourceSoundnessTests
