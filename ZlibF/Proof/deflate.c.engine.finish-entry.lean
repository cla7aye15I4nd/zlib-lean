import ZlibF.Proof.«deflate.c.engine.finish-status»

/-! # Actual accepted BUSY entry for the complete default FINISH path -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Recording a caller's flush request retains the initialized engine
boundary, including both frontiers and the packed symbol contents. -/
theorem last_flush_strategy_boundary {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config) (flush : Int32) :
    StrategyBoundary (setD h ds { d with last_flush := flush }) r ds z
      { d with last_flush := flush } input origin base xs config := by
  have goodA := last_flush_good boundary.good flush
  obtain ⟨pb, buf, trees, ledger, balance⟩ := boundary.symbols
  have ledgerA : SymbolLedger buf { d with last_flush := flush } xs := ledger.keep rfl rfl rfl rfl
  have symbolsA := symbol_boundary_of_ledger goodA trees.base.pbuf trees.base.bytes ledgerA balance
  have chainsA : HeapChains (setD h ds { d with last_flush := flush }) { d with last_flush := flush } d.strstart.toNat :=
    (boundary.chains.at.keep rfl rfl rfl rfl rfl rfl rfl rfl rfl).collapse rfl
  have pendingA : HeapChains (setD h ds { d with last_flush := flush }) { d with last_flush := flush }
      (d.strstart.toNat - d.insert.toNat) :=
    (boundary.frontier.at.keep rfl rfl rfl rfl rfl rfl rfl rfl rfl).collapse rfl
  have contentA : ContentBoundary (setD h ds { d with last_flush := flush }) r ds z
      { d with last_flush := flush } input origin base xs :=
    { boundary.toContentBoundary with good := goodA, chains := chainsA, frontier := pendingA, symbols := symbolsA }
  exact ⟨contentA, boundary.configuration, ⟨boundary.clear.bl, boundary.clear.opt, boundary.clear.fixed⟩, boundary.bits, boundary.strict, boundary.resume⟩

/-- Recording the flush request retains the earlier EOF hash frontier. -/
theorem last_flush_end_frontier {h : Heap} {ds : Nat} {d : DeflateState}
    (frontier : EndFrontier h d) (flush : Int32) :
    EndFrontier (setD h ds { d with last_flush := flush }) { d with last_flush := flush } :=
  (frontier.at.keep rfl rfl rfl rfl rfl rfl rfl rfl rfl).collapse rfl

/-- The actual positive-output BUSY entry records FINISH and reaches
the data path. The legal last-flush range makes the source's rank
evaluation total even though the duplicate-flush refusal is disabled. -/
theorem public_busy_finish_entry {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (status : d.status = BUSY_STATE) (pending : d.pending = 0)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) :
    deflate (some r) Z_FINISH h =
      publicDataTail (some r) (some (.tab ds)) Z_FINISH
        (setD h ds { d with last_flush := Z_FINISH }) := by
  have good0 := last_flush_good good Z_FINISH
  have header : publicZlibHeader (some r) (some (.tab ds))
      (publicDataTail (some r) (some (.tab ds)) Z_FINISH)
      (setD h ds { d with last_flush := Z_FINISH }) =
      publicDataTail (some r) (some (.tab ds)) Z_FINISH (setD h ds { d with last_flush := Z_FINISH }) := by
    unfold publicZlibHeader
    simp only [bind_app, rdD_eq, setD_dstates_same, status,
      show (BUSY_STATE == INIT_STATE) = false from rfl, Bool.false_and, Bool.false_eq_true, ite_false]
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases empty : z.avail_in = 0
    · simp [empty]
    · simp [inputValid empty]
  obtain ⟨rank, ranked⟩ := rank_legal_last_flush d.last_flush lower upper
  have checked := stateCheck_live good.live
  have rankFinish : RANK Z_FINISH = pure 8 := by rfl
  rw [public_deflate_source]
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    show (Z_FINISH > Z_BLOCK) = False from by decide, show (Z_FINISH < 0) = False from by decide,
    decide_false, Bool.false_eq_true, ite_false,
    zrd_eq, good.live.hz, good.live.zst, castDeflateState,
    ldZStream_ok good.live.hz, ldDeflateState_tab good.live.hs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    inputs, Bool.or_false, status, show (BUSY_STATE == FINISH_STATE) = false from rfl, Bool.false_and,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,
    wrD_eq, good.live.hs, pending, show ((0 : UInt64) != 0) = false from rfl,
    rankFinish, ranked, show (Z_FINISH != Z_FINISH) = false from rfl,
    Bool.and_false, rdD_eq, setD_dstates_same, ZStreamRef.get_setD]
  simpa only [status, pending] using header

end Zlib.Deflate.Engine.Proofs
