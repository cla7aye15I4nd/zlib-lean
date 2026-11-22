import ZlibF.Proof.«deflate.c.engine.match-advance»
import ZlibF.Proof.«deflate.c.engine.lazy-logical»
import ZlibF.Proof.«deflate.c.engine.slow-source»
import ZlibF.Proof.«deflate.c.engine.tally-literal»
import ZlibF.Proof.«deflate.c.engine.advance»
import ZlibF.Proof.«deflate.c.engine.symbol-boundary»

/-! # Symbol and block-balance preservation by the real slow decisions -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

def emittedMatch (d : DeflateState) : Symbol :=
  ⟨(d.strstart - 1 - d.prev_match).toNat, (d.prev_length - MIN_MATCH_u).toNat⟩

def emittedLiteral (d : DeflateState) (wa : Array UInt8) : Symbol :=
  ⟨0, wa[d.strstart.toNat - 1]!.toNat⟩

/-- The actual deferred-literal branch retains its packed-symbol and block balance facts. -/
theorem slow_literal_symbol_storage {h : Heap} {r : ZStreamRef} {ds w top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (symbol : SymbolBoundary h ds d xs) (chains : HeapChains h d top)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (positive : 1 ≤ d.lookahead.toNat) (previousByte : 1 ≤ d.strstart.toNat)
    (literalBranch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available ≠ 0)
    (space : d.sym_next.toNat + 3 < d.sym_end.toNat)
    (flush : Int32) (st : LoopS) (hash_head : UInt32) :
    let c := wa[d.strstart.toNat - 1]!
    ∃ after,
      slowDecision (some (.tab ds)) flush st hash_head h =
        .ok ((if z.avail_out == 0 then { st with hash_head, bflush := false, ret := some need_more }
          else { st with hash_head, bflush := false }), after) ∧
      DGood after r ds z (advanceOne (literalState d c)) ∧
      HeapChains after (advanceOne (literalState d c)) top ∧
      (advanceOne (literalState d c)).strstart.toNat + (advanceOne (literalState d c)).lookahead.toNat ≤
        (advanceOne (literalState d c)).window_size.toNat ∧
      after.bytes w = some wa ∧
      (advanceOne (literalState d c)).sym_next.toNat < (advanceOne (literalState d c)).sym_end.toNat ∧
      SymbolBoundary after ds (advanceOne (literalState d c)) (xs ++ [emittedLiteral d wa]) ∧
      SlowRecordFrame d (advanceOne (literalState d c)) ∧ ByteFrame h after (DeflateOwned ds d) := by
  let c := wa[d.strstart.toNat - 1]!
  obtain ⟨b, buf, trees, ledger, balance⟩ := symbol
  have credit : deferredCredit d = 1 := by simp [deferredCredit, available]
  rw [credit] at balance
  have strict : d.sym_next.toNat < d.sym_end.toNat := by omega
  have room := literal_room good.inv strict
  let ht := setD (Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)) ds (literalState d c)
  have goodT : DGood ht r ds z (literalState d c) := literal_good_after good trees c room
  have chainsT : HeapChains ht (literalState d c) top :=
    pending_write_chains good chains trees.base.pbuf _ c
  have count := literal_count trees.base room c
  have flag : (d.sym_next + 3 == d.sym_end) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro eq
    have num := congrArg UInt32.toNat eq
    change (literalState d c).sym_next.toNat = d.sym_end.toNat at num
    rw [count] at num
    omega
  have tally : tally_lit (some (.tab ds)) c h = .ok (false, ht) := by
    simpa only [flag] using tally_literal_run trees.base c room
  obtain ⟨w0, p, q, b0, blocks⟩ := good.inv.blocks
  have wid : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  subst w0
  obtain ⟨wa0, get0, size⟩ := blocks.wa
  have array : wa0 = wa := Option.some.inj (get0.symm.trans get)
  subst wa0
  have fit : d.strstart.toNat - 1 < wa.size := by rw [good.inv.wsz] at range; omega
  have sub : (d.strstart - 1).toNat = d.strstart.toNat - 1 := u32_sub_one previousByte
  have read : index8 d.window (d.strstart - 1).toNat h = .ok (c, h) := by
    rw [win, sub]
    simpa [OkOn, fit, c] using index8_ok (off := 0)
      (i := d.strstart.toNat - 1) get (by omega)
  have advanced := advance_one_good goodT chainsT range positive
  let after := setD ht ds (advanceOne (literalState d c))
  have write : wr (some (.tab ds)) advanceOne ht = .ok ((), after) := by
    simp [wrD_eq, goodT.live.hs, after]
  have output : zrd (some r) (·.avail_out) after = .ok (z.avail_out, after) := by
    have getter : r.get after = some z := advanced.1.live.hz
    simp only [zrd_eq, getter]
  have ledgerT : SymbolLedger (literalBytes buf d c) (literalState d c) (xs ++ [emittedLiteral d wa]) :=
    ledger_literal trees.base ledger room c
  have ledgerA : SymbolLedger (literalBytes buf d c) (advanceOne (literalState d c))
      (xs ++ [emittedLiteral d wa]) := ledgerT.keep rfl rfl rfl rfl
  have creditA : deferredCredit (advanceOne (literalState d c)) = 1 := by
    simp [deferredCredit, advanceOne, literalState, available]
  have balanceA : BlockBalance (advanceOne (literalState d c)) (xs ++ [emittedLiteral d wa])
      (deferredCredit (advanceOne (literalState d c))) := by
    rw [creditA]
    exact balance_advance_one goodT.inv range positive (balance_literal balance c)
  have getA : after.bytes b = some (literalBytes buf d c) := by simp [after, ht]
  have symbolA := symbol_boundary_of_ledger advanced.1 trees.base.pbuf getA ledgerA balanceA
  have storageA : ByteFrame h after (DeflateOwned ds d) :=
    (pending_state_byte_frame h ds b d (literalState d c) (literalBytes buf d c) trees.base.pbuf).trans
      ((byte_frame_setD ht ds (advanceOne (literalState d c))).weaken (fun _ equal => Or.inl equal))
  refine ⟨after, ?_, advanced.1, advanced.2.1, advanced.2.2, ?_, literal_not_full trees c room flag, symbolA, rfl, storageA⟩
  · unfold slowDecision
    simp only [bind_app, ldDeflateState_tab good.live.hs, literalBranch, Bool.false_eq_true, ite_false]
    have hasLiteral : (d.match_available != 0) = true := by simpa using available
    simp only [hasLiteral, ite_true, bind_app, read, tally, Bool.false_eq_true, ite_false]
    change (do
      wr (some (.tab ds)) advanceOne
      if (← zrd d.strm (·.avail_out)) == 0 then
        return { st with hash_head, bflush := false, ret := some need_more }
      return { st with hash_head, bflush := false }) ht = _
    rw [bind_app, write]
    simp only [good.live.back, bind_app, output]
    by_cases full : (z.avail_out == 0) = true <;> simp [full]
  · exact pending_window_frame good win trees.base.pbuf get (literalBytes buf d c)
      (advanceOne (literalState d c))

/-- Deferring a byte adds one unit of credit and does not emit a symbol. -/
theorem slow_defer_symbol_boundary {h : Heap} {r : ZStreamRef} {ds top : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol}
    (good : DGood h r ds z d) (symbol : SymbolBoundary h ds d xs) (chains : HeapChains h d top)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (positive : 1 ≤ d.lookahead.toNat)
    (branch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available = 0) (flush : Int32) (st : LoopS) (candidate : UInt32) :
    slowDecision (some (.tab ds)) flush st candidate h =
      .ok ({ st with hash_head := candidate, bflush := false }, setD h ds (deferOne d)) ∧
    SymbolBoundary (setD h ds (deferOne d)) ds (deferOne d) xs ∧ SlowRecordFrame d (deferOne d) := by
  obtain ⟨b, buf, trees, ledger, balance⟩ := symbol
  have credit : deferredCredit d = 0 := by simp [deferredCredit, available]
  rw [credit] at balance
  have goodA := (defer_one_good good chains range positive).1
  have ledgerA : SymbolLedger buf (deferOne d) xs := ledger.keep rfl rfl rfl rfl
  have creditA : deferredCredit (deferOne d) = 1 := by simp [deferredCredit, deferOne]
  have balanceA : BlockBalance (deferOne d) xs (deferredCredit (deferOne d)) := by
    rw [creditA]
    exact balance_advance_one good.inv range positive balance
  exact ⟨slow_defer_branch good.live.hs branch available flush st candidate,
    symbol_boundary_of_ledger goodA trees.base.pbuf trees.base.bytes ledgerA balanceA, rfl⟩

end Zlib.Deflate.Engine.Proofs
