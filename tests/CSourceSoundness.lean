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

/-- Casts emitted for the tree builder, including negative signed operands. -/
example (x : Int32) : evalCast .u32 (.i32 x) = .ok (.u32 (Zlib.Trees.i2u x)) := rfl
example (x : Int32) : evalCast .u64 (.i32 x) = .ok (.u64 (Zlib.Trees.i2ul x)) := rfl
example (x : Int32) : evalCast .u16 (.i32 x) = .ok (.u16 (Zlib.Trees.i2us x)) := rfl
example (x : UInt32) : evalCast .i32 (.u32 x) = .ok (.i32 (Zlib.Trees.u2i x)) := by
  change Except.ok (.i32 (Int32.ofInt (x.toNat : Int))) = (Except.ok (.i32 _) : Except C.Fault CVal)
  unfold Zlib.Trees.u2i
  split
  · congr 2
    apply Int32.toBitVec_inj.mp
    simp [BitVec.ofInt]
  · rfl

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

namespace CSourceAddressTests
open C Lean2C.CSource Lean2C.Semantics

/-- Two unsigned long elements with distinguishable first bytes. -/
private def memory : Heap :=
  { Heap.empty with bytes := upd Heap.empty.bytes 0 (some #[1,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0]) }

private def ptr : Value := .var (.ptr .u64) "p"
private def index (i : Nat) : Value := .index .u64 ptr (.num .i32 i)
private def outcome (ss : List Stmt) (p : BPtr := .ref (.blk 0) 0) : Except Fault CVal :=
  match runCFn (fun _ => none) [] 0 ([("p", .ptr .u64)], ss) [.ptr p] memory with
  | .ret v _ => .ok v
  | .fault fault => .error fault
  | _ => .error (.ub "fixture function did not return")

#guard (outcome [.ret (index 1)]).toOption == some (.u64 2)
#guard (outcome [.assign (index 1) (.num .u64 17), .ret (index 0)]).toOption == some (.u64 1)
#guard (outcome [.assign (index 1) (.num .u64 17), .ret (index 1)]).toOption == some (.u64 17)
#guard (outcome [.ret (.load .u64 (.op (.ptr .u64) "+" (.num .i32 1) ptr))]).toOption == some (.u64 2)
#guard (outcome [.ret (.op .i64 "-" ptr (.op (.ptr .u64) "+" ptr (.num .i32 2)))]).toOption == some (.i64 (-2))
#guard (outcome [.ret (.load .u64 (.op (.ptr .u64) "-" ptr (.num .i32 1)))] (.ref (.blk 0) 8)).toOption == some (.u64 1)
#guard (outcome [.ret (index 2)]) matches .error (.ub "read outside its object")
#guard (outcome [.ret (index 0)] (.ref (.blk 0) 1)) matches .error (.ub "misaligned unsigned long load")
#guard (outcome [.assign (index 0) (.num .u64 17), .ret (.num .i32 0)] (.ref (.blk 0) 1)) matches .error (.ub "misaligned unsigned long store")
#guard (outcome [.ret (.op (.ptr .u64) "+" ptr (.num .i32 0))] .null) matches .error (.ub "arithmetic on a null pointer")

/-- The legacy cell contract admits the eight bytes starting at offset one.
The same concrete heap distinguishes the bytewise read from the typed C read. -/
example :
    ZlibF.Spec.Public.LengthCell memory (.ref (.blk 0) 1) 0x0200000000000000 ∧
    C.load64 (.ref (.blk 0) 1) memory = .ok (0x0200000000000000, memory) ∧
    readHeap .u64 (.ref (.blk 0) 1) memory = .error (.ub "misaligned unsigned long load") := by
  have cell : ZlibF.Spec.Public.LengthCell memory (.ref (.blk 0) 1) 0x0200000000000000 :=
    ⟨Or.inr ⟨.blk 0, 1, _, rfl, rfl, by decide, by decide⟩,
     Or.inr ⟨.blk 0, 1, _, rfl, rfl, rfl, by decide⟩⟩
  exact ⟨cell, ZlibF.Spec.Public.Proofs.Uncompress.load64_cell cell, rfl⟩

end CSourceAddressTests
