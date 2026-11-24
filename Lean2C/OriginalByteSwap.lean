import Lean2C.Soundness

/-! Typed byte-swap expressions from the two pinned Linux translation units. -/

namespace Lean2C.OriginalByteSwap
open CSource Semantics Soundness

private def word : Value := .var .u32 "word"

private def lowPiece (op : String) (mask count : Nat) : Value :=
  .op .u32 op (.op .u32 "&" word (.cast .u32 (.num .i32 mask))) (.num .i32 count)

private def assemble (ty : Ty) (first second third fourth : Value) : Value :=
  .op ty "|" (.op ty "|" (.op ty "|" first second) third) fourth

/-- On the pinned Linux target, the unsuffixed hexadecimal 0xff000000 has type unsigned int. -/
def original : List (String × Ty) × List Stmt :=
  ([("word", .u32)], [.ret (assemble .u32
    (.op .u32 ">>" (.op .u32 "&" word (.num .u32 4278190080)) (.num .i32 24))
    (lowPiece ">>" 16711680 8) (lowPiece "<<" 65280 8) (lowPiece "<<" 255 24))])

/-- The standalone emitter spells that mask in decimal. Clang widens the first mask
and all three ORs to signed long and converts the return value back to unsigned int. -/
def standalone : List (String × Ty) × List Stmt :=
  ([("word", .u32)], [.ret (.cast .u32 (assemble .i64
    (.op .i64 ">>" (.op .i64 "&" (.cast .i64 word) (.num .i64 4278190080)) (.num .i32 24))
    (.cast .i64 (lowPiece ">>" 16711680 8)) (.cast .i64 (lowPiece "<<" 65280 8))
    (.cast .i64 (lowPiece "<<" 255 24))))])

private def wide (x : UInt32) : Int64 := x.toUInt64.toInt64

private theorem wide_int (x : UInt32) : (wide x).toInt = (x.toNat : Int) := by
  change x.toUInt64.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_cond]
  have bound := x.toNat_lt
  simp
  omega

private theorem cast_wide (x : UInt32) : evalCast .i64 (.u32 x) = .ok (.i64 (wide x)) := by
  simp only [evalCast,CVal.toInt?,ofIntForTy]
  change Except.ok (.i64 (Int64.ofInt (x.toNat : Int)) : CVal) = _
  rw [← wide_int x, Int64.ofInt_toInt]

private theorem unsigned_self (x : UInt32) : evalCast .u32 (.u32 x) = .ok (.u32 x) := by
  simp only [evalCast,CVal.toInt?,ofIntForTy,Except.ok.injEq,CVal.u32.injEq]
  apply UInt32.toNat_inj.mp
  change ((x.toNat : Int) % (2^32 : Int)).toNat % 2^32 = x.toNat
  rw [show (2^32 : Int) = ((2^32 : Nat) : Int) by decide, ← Int.natCast_emod, Int.toNat_natCast,
    Nat.mod_eq_of_lt x.toNat_lt, Nat.mod_eq_of_lt x.toNat_lt]

private theorem cast_back (x : UInt32) : evalCast .u32 (.i64 (wide x)) = .ok (.u32 x) := by
  simpa only [evalCast, CVal.toInt?, wide_int, Int.ofNat_eq_natCast] using unsigned_self x

private theorem signed_self (x : Int64) : evalCast .i64 (.i64 x) = .ok (.i64 x) := by
  simp [evalCast, CVal.toInt?, ofIntForTy]

private theorem wide_and (x y : UInt32) : wide x &&& wide y = wide (x &&& y) := by simp [wide]
private theorem wide_or (x y : UInt32) : wide x ||| wide y = wide (x ||| y) := by simp [wide]

private theorem div24 (x : UInt32) :
    Int64.ofInt ((wide x).toInt / (2^24 : Int)) = wide (x >>> 24) := by
  rw [wide_int, ← Int64.ofInt_toInt (wide (x >>> 24)), wide_int]
  congr 1
  simp [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Int.natCast_ediv]

private theorem long_and (x y : UInt32) (h : C.Heap) :
    evalBinOp .i64 "&" (.i64 (wide x)) (.i64 (wide y)) h = .ok (.i64 (wide (x &&& y))) := by
  simp [evalBinOp, Bind.bind, Except.bind, Pure.pure, Except.pure, wide_and]

private theorem long_or (x y : UInt32) (h : C.Heap) :
    evalBinOp .i64 "|" (.i64 (wide x)) (.i64 (wide y)) h = .ok (.i64 (wide (x ||| y))) := by
  simp [evalBinOp, Bind.bind, Except.bind, Pure.pure, Except.pure, wide_or]

private theorem long_shr (x : UInt32) (h : C.Heap) :
    evalBinOp .i64 ">>" (.i64 (wide x)) (.i32 24) h = .ok (.i64 (wide (x >>> 24))) := by
  unfold evalBinOp evalShiftOp
  simp only [show ["<", "<=", ">", ">=", "==", "!="].contains ">>" = false from rfl,
    show (">>" == "<<") = false from rfl, show (">>" == ">>") = true from rfl,
    Bool.false_or, Bool.or_true, bitWidth?, CVal.toInt?, signed_self,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact congrArg (fun z => (Except.ok (CVal.i64 z) : Except C.Fault CVal)) (div24 x)

section
variable (f : FnTable) (g : CEnv) (fuel : Nat) (x : UInt32) (h : C.Heap)
private abbrev Valued (expr : Value) (v : CVal) : Prop :=
  evalValue f g fuel [("word", .u32 x)] h expr = .ok (v, [("word", .u32 x)], h)

private theorem low_piece (op : String) (mask count : Nat) (out : UInt32)
    (bounds : mask < 2 ^ 31 ∧ count < 2 ^ 31)
    (hm : evalCast .u32 (.i32 (Int32.ofNat mask)) = .ok (.u32 (UInt32.ofNat mask)))
    (h1 : (op == "&&") = false) (h2 : (op == "||") = false)
    (shift : evalBinOp .u32 op (.u32 (x &&& UInt32.ofNat mask)) (.i32 (Int32.ofNat count)) h = .ok (.u32 out)) :
    Valued f g fuel x h (lowPiece op mask count) (.u32 out) := by
  exact evalValue_op _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2
    (evalValue_op _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl
      (evalValue_var _ _ _ _ _ _ _ _ rfl)
      (evalValue_cast _ _ _ _ _ _ _ _ _ _ _ (evalValue_num _ _ _ _ _ _ _ _ (ite_eq_left bounds.1)) hm)
      (evalBinOp_u32_and _ _ h))
    (evalValue_num _ _ _ _ _ _ _ _ (ite_eq_left bounds.2)) shift

private theorem original_high :
    Valued f g fuel x h
      (.op .u32 ">>" (.op .u32 "&" word (.num .u32 4278190080)) (.num .i32 24))
      (.u32 ((x &&& 0xff000000) >>> 24)) :=
  evalValue_op _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl
    (evalValue_op _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl
      (evalValue_var _ _ _ _ _ _ _ _ rfl) (evalValue_num _ _ _ _ _ _ _ _ rfl)
      (evalBinOp_u32_and x 0xff000000 h))
    (evalValue_num _ _ _ _ _ _ _ _ rfl) (evalBinOp_u32_shr _ 24 (by decide) h)

private theorem standalone_high :
    Valued f g fuel x h
      (.op .i64 ">>" (.op .i64 "&" (.cast .i64 word) (.num .i64 4278190080)) (.num .i32 24))
      (.i64 (wide ((x &&& 0xff000000) >>> 24))) :=
  evalValue_op _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl
    (evalValue_op _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl
      (evalValue_cast _ _ _ _ _ _ _ _ _ _ _ (evalValue_var _ _ _ _ _ _ _ _ rfl) (cast_wide x))
      (evalValue_num _ _ _ _ _ _ _ _ rfl) (long_and x 0xff000000 h))
    (evalValue_num _ _ _ _ _ _ _ _ rfl) (long_shr _ h)

private theorem join32 {a b : Value} {y z : UInt32}
    (ha : Valued f g fuel x h a (.u32 y)) (hb : Valued f g fuel x h b (.u32 z)) :
    Valued f g fuel x h (.op .u32 "|" a b) (.u32 (y ||| z)) :=
  evalValue_op _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl ha hb (evalBinOp_u32_or _ _ h)

private theorem join64 {a b : Value} {y z : UInt32}
    (ha : Valued f g fuel x h a (.i64 (wide y))) (hb : Valued f g fuel x h b (.i64 (wide z))) :
    Valued f g fuel x h (.op .i64 "|" a b) (.i64 (wide (y ||| z))) :=
  evalValue_op _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl ha hb (long_or _ _ h)

private theorem widen {a : Value} {y : UInt32} (ha : Valued f g fuel x h a (.u32 y)) :
    Valued f g fuel x h (.cast .i64 a) (.i64 (wide y)) :=
  evalValue_cast _ _ _ _ _ _ _ _ _ _ _ ha (cast_wide y)

/-- The typed original body returns the byte-swapped word and preserves every heap. -/
theorem original_sound :
    runCFn f g fuel original [.u32 x] h = .ret (.u32 (Zlib.Crc32.byte_swap x)) h := by
  have p1 := low_piece f g fuel x h ">>" 16711680 8 _ (by decide) rfl rfl rfl (evalBinOp_u32_shr _ 8 (by decide) h)
  have p2 := low_piece f g fuel x h "<<" 65280 8 _ (by decide) rfl rfl rfl (evalBinOp_u32_shl _ 8 (by decide) h)
  have p3 := low_piece f g fuel x h "<<" 255 24 _ (by decide) rfl rfl rfl (evalBinOp_u32_shl _ 24 (by decide) h)
  have top := original_high f g fuel x h
  have j1 := join32 f g fuel x h top p1
  have j2 := join32 f g fuel x h j1 p2
  have j3 := join32 f g fuel x h j2 p3
  unfold runCFn original
  simp only [bindParams, unsigned_self, Bind.bind, Except.bind, Pure.pure, Except.pure]
  apply execStmts_ret
  exact j3

/-- The typed standalone body returns the byte-swapped word and preserves every heap. -/
theorem standalone_sound :
    runCFn f g fuel standalone [.u32 x] h = .ret (.u32 (Zlib.Crc32.byte_swap x)) h := by
  have p1 := low_piece f g fuel x h ">>" 16711680 8 _ (by decide) rfl rfl rfl (evalBinOp_u32_shr _ 8 (by decide) h)
  have p2 := low_piece f g fuel x h "<<" 65280 8 _ (by decide) rfl rfl rfl (evalBinOp_u32_shl _ 8 (by decide) h)
  have p3 := low_piece f g fuel x h "<<" 255 24 _ (by decide) rfl rfl rfl (evalBinOp_u32_shl _ 24 (by decide) h)
  have top := standalone_high f g fuel x h
  have j1 := join64 f g fuel x h top (widen f g fuel x h p1)
  have j2 := join64 f g fuel x h j1 (widen f g fuel x h p2)
  have j3 := join64 f g fuel x h j2 (widen f g fuel x h p3)
  unfold runCFn standalone
  simp only [bindParams, unsigned_self, Bind.bind, Except.bind, Pure.pure, Except.pure]
  apply execStmts_ret
  exact evalValue_cast _ _ _ _ _ _ _ _ _ _ _ j3 (cast_back _)

/-- Both actual source bodies agree on the returned value and the entire final heap. -/
theorem same_byte_swap :
    runCFn f g fuel original [.u32 x] h = runCFn f g fuel standalone [.u32 x] h := by
  rw [original_sound, standalone_sound]

end

#print axioms same_byte_swap

end Lean2C.OriginalByteSwap
