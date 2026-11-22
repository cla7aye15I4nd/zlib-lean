import ZlibF.Proof.«inffast.c.copy»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec

theorem matchArr_size (wsize wnext woff : Nat) (W : Array UInt8) (bg o dist len : Nat) (A : Array UInt8) :
    (matchArr wsize wnext woff W bg o dist len A).size = A.size := by
  unfold matchArr
  dsimp only
  repeat' split
  all_goals simp [blitN_size, cpyN_size]

theorem EnvG.mArr_sep {α : Bool} (e : EnvG α) (sep : ¬ (α = true ∧ BRef.blk e.wb = e.ob)) (bg o dist len : Nat)
    (A : Array UInt8) :
    e.mArr bg o dist len A = matchArr e.s0.wsize.toNat e.s0.wnext.toNat e.woff e.W bg o dist len A := by
  cases α with
  | false => rfl
  | true =>
    have ne : ¬ BRef.blk e.wb = e.ob := fun x => sep ⟨rfl, x⟩
    simp only [EnvG.mArr, ne, ite_false]

theorem EnvG.mArr_alias (e : EnvG true) (same : BRef.blk e.wb = e.ob) (bg o dist len : Nat) (A : Array UInt8) :
    e.mArr bg o dist len A = matchArrA e.s0.wsize.toNat e.woff bg o dist len A := by
  simp only [EnvG.mArr, same, ite_true]

theorem matchArrA_size (wsize woff : Nat) (bg o dist len : Nat) (A : Array UInt8) :
    (matchArrA wsize woff bg o dist len A).size = A.size := by
  unfold matchArrA
  dsimp only
  repeat' split
  all_goals simp [cpyN_size]

/-- A match within the current call's output copies from the output, whatever the window. -/
theorem EnvG.mArr_near {α : Bool} (e : EnvG α) {bg o dist len : Nat} {A : Array UInt8} (near : ¬ (o - bg < dist)) :
    e.mArr bg o dist len A = cpyN len (o - dist) o A := by
  cases α with
  | false => simp [EnvG.mArr, matchArr, near]
  | true =>
    simp only [EnvG.mArr]
    split
    · simp [matchArrA, near]
    · simp [matchArr, near]

theorem EnvG.mArr_size {α : Bool} (e : EnvG α) (bg o dist len : Nat) (A : Array UInt8) :
    (e.mArr bg o dist len A).size = A.size := by
  cases α with
  | false => exact matchArr_size _ _ _ _ _ _ _ _ _
  | true =>
    simp only [EnvG.mArr]
    split
    · exact matchArrA_size _ _ _ _ _ _ _
    · exact matchArr_size _ _ _ _ _ _ _ _ _



variable {α : Bool} {e : EnvG α} {c : Ctx}

theorem EnvG.heap_ldstate (hc : CtxOK e c) (A msg m) :
    ldInflateState c.state (e.heap A msg m) = .ok ({ e.s0 with mode := m }, e.heap A msg m) := by
  rw [hc.state]
  apply ldInflateState_ok
  simp [InflateStateRef.get, e.heap_istates]

theorem EnvG.heap_ldstrm (hc : CtxOK e c) (A msg m) :
    ldZStream c.strm (e.heap A msg m) = .ok ({ e.sm0 with msg := msg }, e.heap A msg m) := by
  rw [hc.strm, e.hstrm]
  exact ldZStream_ok (e.heap_rget A msg m)

/-- Setting the mode of the state: the heap `e.heap A msg m` becomes `e.heap A msg m'`. -/
theorem EnvG.heap_stmode (hc : CtxOK e c) (A msg m m') (s : InflateState) (hs : s = { e.s0 with mode := m' }) :
    stInflateState c.state s (e.heap A msg m) = .ok ((), e.heap A msg m') := by
  rw [hc.state, hs]
  have hg : (InflateStateRef.tab e.stid).get (e.heap A msg m) = some { e.s0 with mode := m } := by
    simp [InflateStateRef.get, e.heap_istates]
  rw [stInflateState_ok hg rfl, InflateStateRef.put_tab (by simpa [InflateStateRef.get] using hg)]
  exact congrArg (fun h => Except.ok ((), h)) (e.heap_setI A msg m m')

theorem EnvG.heap_stmsg (hc : CtxOK e c) (A msg m) (p : BPtr) (sm : ZStream) (hs : sm = { e.sm0 with msg := p }) :
    stZStream c.strm sm (e.heap A msg m) = .ok ((), e.heap A p m) := by
  rw [hc.strm, e.hstrm, hs]
  rw [stZStream_ok (e.heap_rget A msg m) e.hrw]
  exact congrArg (fun h => Except.ok ((), h)) (e.heap_msg A msg p m)

/-- `strm->msg = "..."; state->mode = BAD;` -/
theorem badData_run (hc : CtxOK e c) (A msg m) (s : String) (hs : s ∈ strTable) :
    ∃ i, badData c s (e.heap A msg m) = .ok ((), e.heap A (.ref (BRef.str i) 0) BAD) := by
  obtain ⟨i, hi, _⟩ := strLitRef_of_mem (h := e.heap A msg m) hs
  refine ⟨i, ?_⟩
  unfold badData Zlib.Zutil.strLit
  rw [bind_ok hi, bind_ok (e.heap_ldstrm hc A msg m), bind_ok (e.heap_stmsg hc A msg m _ _ rfl),
    bind_ok (e.heap_ldstate hc A _ m), e.heap_stmode hc A _ m BAD _ rfl]


/-- `copyMatch`: either the match is copied (the output block becomes `matchArr ..`, `out` advances by `len`), or the
distance is too far back (message and mode `BAD`, `broke`). -/
theorem WinRel.ne {α : Bool} {wb : Nat} {ob : BRef} {wn : UInt32} {P : Prop} (r : WinRel α wb ob wn P)
    (al : ¬ (α = true ∧ BRef.blk wb = ob)) : BRef.blk wb ≠ ob := by
  cases α with
  | false => exact r
  | true => exact fun x => al ⟨rfl, x⟩

theorem copyMatch_run (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (o : Nat)
    (hout : l.out = .ref e.ob o) (hbg : e.bg ≤ o) (hop : l.op.toNat = o - e.bg)
    (hdist : 1 ≤ l.dist.toNat) (hlen : 3 ≤ l.len.toNat) (hroom : o + l.len.toNat ≤ A.size)
    (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (hbroke : l.broke = false) :
    Wp (copyMatch c l) (e.heap A msg m) (fun l' h' =>
      l'.in_ = l.in_ ∧ l'.hold = l.hold ∧ l'.bits = l.bits ∧ l'.againL = l.againL ∧ l'.againD = l.againD ∧
      ((l'.broke = false ∧ l'.out = .ref e.ob (o + l.len.toNat) ∧
          h' = e.heap (e.mArr e.bg o l.dist.toNat l.len.toNat A) msg m) ∨
       (l'.broke = true ∧ ∃ p, h' = e.heap A p BAD ∧ l'.out = l.out))) := by
  have hoA : o ≤ A.size := by omega
  unfold copyMatch
  dsimp only
  by_cases hd : l.dist > l.op
  · simp only [hd, ite_true]
    have hd1 : l.op.toNat < l.dist.toNat := UInt32.lt_iff_toNat_lt.mp hd
    have hop1 : (l.dist - l.op).toNat = l.dist.toNat - (o - e.bg) := by
      rw [u32_toNat_sub (by omega)]; omega
    by_cases hw : l.dist - l.op > c.whave
    · -- too far back
      simp only [hw, ite_true]
      refine Wp.bindO (e.heap_ldstate hc A msg m) ?_
      have hsane : (({ e.s0 with mode := m } : InflateState).sane != 0) = true := by
        simp only [bne_iff_ne, ne_eq]; exact e.hsane
      simp only [hsane, ite_true]
      obtain ⟨i, hi⟩ := badData_run hc A msg m "invalid distance too far back" (by decide +kernel)
      refine Wp.bindE hi ?_
      refine Wp.pure' ?_
      exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inr ⟨rfl, _, rfl, rfl⟩⟩
    · simp only [hw, ite_false]
      have hw' : (l.dist - l.op).toNat ≤ c.whave.toNat := by
        have h1 : ¬ (c.whave < l.dist - l.op) := hw
        have h2 : ¬ (c.whave.toNat < (l.dist - l.op).toNat) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr h)
        omega
      have hwh : c.whave.toNat ≤ c.wsize.toNat := by rw [hc.whave, hc.wsize]; exact e.hwh
      have hwn : c.wnext.toNat ≤ c.wsize.toNat := by rw [hc.wnext, hc.wsize]; exact e.hwn
      have hws : c.wsize.toNat ≤ 32768 := by rw [hc.wsize]; exact e.hws
      have hwne : e.s0.whave ≠ 0 := by
        intro h0
        have : c.whave.toNat = 0 := by rw [hc.whave, h0]; rfl
        omega
      obtain ⟨hwptr, hrel, hWb, hWsz⟩ := e.hwin hwne
      by_cases al : α = true ∧ BRef.blk e.wb = e.ob
      · -- the window is the output block (`inflateBack`): every copy reads the current block
        obtain ⟨rfl, same⟩ := al
        obtain ⟨hn0e, hinside⟩ := hrel same
        rw [e.mArr_alias same]
        have hwptr' : c.window = Ptr.ref e.ob e.woff := by rw [hc.window, hwptr, same]
        have hAg : Space.get (e.heap A msg m) e.ob = some A := e.heap_bytes_ob A msg m
        have hn0 : c.wnext = 0 := by rw [hc.wnext]; exact hn0e
        have hn0' : (c.wnext == 0) = true := by simp [hn0]
        simp only [hn0', ite_true]
        have hwsz : c.wsize.toNat = e.s0.wsize.toNat := by rw [hc.wsize]
        have hsubw : (c.wsize - (l.dist - l.op)).toNat = c.wsize.toNat - (l.dist.toNat - (o - e.bg)) := by
          rw [u32_toNat_sub (by omega), hop1]
        have hwend : e.woff + c.wsize.toNat ≤ A.size := by rw [hwsz]; omega
        have hadd : OkOn (e.heap A msg m) (Ptr.add c.window ↑(c.wsize - (l.dist - l.op)).toNat)
            (Ptr.ref e.ob (e.woff + (c.wsize.toNat - (l.dist.toNat - (o - e.bg))))) := by
          rw [hwptr', hsubw]
          exact Ptr.add_nat_ok hAg (by omega)
        refine Wp.bindO hadd ?_
        generalize l.dist - l.op = op1 at hop1 hw' hadd ⊢
        by_cases hlt : op1 < l.len
        · simp only [hlt, ite_true]
          have hlt' : op1.toNat < l.len.toNat := UInt32.lt_iff_toNat_lt.mp hlt
          have hlen1 : (l.len - op1).toNat = l.len.toNat - op1.toNat := u32_toNat_sub (by omega)
          refine Wp.bindE (copyOp_out e A msg m
            { l with op := op1, len := l.len - op1, from_ := Ptr.ref e.ob (e.woff + (c.wsize.toNat - (l.dist.toNat - (o - e.bg)))) }
            op1.toNat (e.woff + (c.wsize.toNat - (l.dist.toNat - (o - e.bg)))) o rfl (by omega) rfl hout
            (by omega) (by omega)) ?_
          dsimp only
          generalize hA1 : cpyN op1.toNat (e.woff + (c.wsize.toNat - (l.dist.toNat - (o - e.bg)))) o A = A1
          have hA1sz : A1.size = A.size := by rw [← hA1]; exact cpyN_size _ _ _ _
          have hsub2 : OkOn (e.heap A1 msg m) (subn (Ptr.ref e.ob (o + op1.toNat)) l.dist)
              (Ptr.ref e.ob (o + op1.toNat - l.dist.toNat)) :=
            subn_ok (r := e.ob) (a := A1) (e.heap_bytes_ob A1 msg m) (by omega) (by omega)
          refine Wp.bindO hsub2 ?_
          refine Wp.of_eq (a := _) (h' := _) (tailW_run (Src.out e) A1 msg m
            { l with out := Ptr.ref e.ob (o + op1.toNat), op := 0, len := l.len - op1,
                     from_ := Ptr.ref e.ob (o + op1.toNat - l.dist.toNat) }
            (l.len - op1).toNat (o + op1.toNat - l.dist.toNat) (o + op1.toNat) rfl rfl rfl (by simp; omega)
            (by omega)) ?_
          refine ⟨rfl, rfl, rfl, rfl, rfl, Or.inl ⟨hbroke, ?_, ?_⟩⟩
          · simp only [hlen1]; rw [show o + op1.toNat + (l.len.toNat - op1.toNat) = o + l.len.toNat by omega]
          · simp only [hlen1]
            rw [cpyG_id]
            unfold matchArrA
            have h1 : o - e.bg < l.dist.toNat := by omega
            simp only [h1, ite_true]
            have h3 : op1.toNat = l.dist.toNat - (o - e.bg) := hop1
            have h4' : l.dist.toNat - (o - e.bg) < l.len.toNat := by omega
            have h5 : e.woff + (c.wsize.toNat - (l.dist.toNat - (o - e.bg))) =
                e.woff + e.s0.wsize.toNat - (l.dist.toNat - (o - e.bg)) := by omega
            simp only [h3, h4'] at hA1 ⊢
            rw [h5] at hA1
            rw [← hA1]
            try simp
        · simp only [hlt, ite_false]
          have hlt' : l.len.toNat ≤ op1.toNat := by
            have h1 : ¬ (op1 < l.len) := hlt
            have h2 : ¬ (op1.toNat < l.len.toNat) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr h)
            omega
          refine Wp.of_eq (a := _) (h' := _) (tailW_run (Src.out e) A msg m
            { l with op := op1, from_ := Ptr.ref e.ob (e.woff + (c.wsize.toNat - (l.dist.toNat - (o - e.bg)))) }
            l.len.toNat (e.woff + (c.wsize.toNat - (l.dist.toNat - (o - e.bg)))) o rfl rfl hout
            (by show _ ≤ (id A).size; simp only [id]; omega) (by omega)) ?_
          refine ⟨rfl, rfl, rfl, rfl, rfl, Or.inl ⟨hbroke, rfl, ?_⟩⟩
          rw [cpyG_id]
          unfold matchArrA
          have h1 : o - e.bg < l.dist.toNat := by omega
          have h3 : op1.toNat = l.dist.toNat - (o - e.bg) := hop1
          have h4' : ¬ (l.dist.toNat - (o - e.bg) < l.len.toNat) := by omega
          have h5 : e.woff + (c.wsize.toNat - (l.dist.toNat - (o - e.bg))) =
              e.woff + e.s0.wsize.toNat - (l.dist.toNat - (o - e.bg)) := by omega
          simp only [h1, h4', ite_true, ite_false, h5]
      have hwb : BRef.blk e.wb ≠ e.ob := WinRel.ne hrel al
      rw [e.mArr_sep al]
      have hwptr' : c.window = Ptr.ref (BRef.blk e.wb) e.woff := by rw [hc.window]; exact hwptr
      have hsrc : Src e (BRef.blk e.wb) (fun _ => e.W) := Src.win e (BRef.blk e.wb) e.W hwb hWb
      have hWg : Space.get (e.heap A msg m) (BRef.blk e.wb) = some e.W := by
        rw [e.heap_get_ne A msg m hwb]; exact hWb
      have hwsz : c.wsize.toNat = e.s0.wsize.toNat := by rw [hc.wsize]
      have hwnx : c.wnext.toNat = e.s0.wnext.toNat := by rw [hc.wnext]
      by_cases hn0 : c.wnext = 0
      · -- (i) the window has not wrapped
        have hn0' : (c.wnext == 0) = true := by simp [hn0]
        simp only [hn0', ite_true]
        have hsubw : (c.wsize - (l.dist - l.op)).toNat = c.wsize.toNat - (l.dist.toNat - (o - e.bg)) := by
          rw [u32_toNat_sub (by omega), hop1]
        have hadd : OkOn (e.heap A msg m) (Ptr.add c.window ↑(c.wsize - (l.dist - l.op)).toNat)
            (Ptr.ref (BRef.blk e.wb) (e.woff + (c.wsize.toNat - (l.dist.toNat - (o - e.bg))))) := by
          rw [hwptr', hsubw]
          exact Ptr.add_nat_ok hWg (by omega)
        refine Wp.bindO hadd ?_
        generalize l.dist - l.op = op1 at hop1 hw' hadd ⊢
        by_cases hlt : op1 < l.len
        · simp only [hlt, ite_true]
          have hlt' : op1.toNat < l.len.toNat := UInt32.lt_iff_toNat_lt.mp hlt
          have hlen1 : (l.len - op1).toNat = l.len.toNat - op1.toNat := u32_toNat_sub (by omega)
          refine Wp.bindE (copyOp_win e e.W msg m (BRef.blk e.wb) hwb hWb A
            { l with op := op1, len := l.len - op1, from_ := Ptr.ref (BRef.blk e.wb) (e.woff + (c.wsize.toNat - (l.dist.toNat - (o - e.bg)))) }
            op1.toNat (e.woff + (c.wsize.toNat - (l.dist.toNat - (o - e.bg)))) o rfl (by omega) rfl hout
            (by omega) (by omega)) ?_
          dsimp only
          generalize hA1 : blitN e.W op1.toNat (e.woff + (c.wsize.toNat - (l.dist.toNat - (o - e.bg)))) o A = A1
          have hA1sz : A1.size = A.size := by rw [← hA1]; exact blitN_size _ _ _ _ _
          have hsub2 : OkOn (e.heap A1 msg m) (subn (Ptr.ref e.ob (o + op1.toNat)) l.dist)
              (Ptr.ref e.ob (o + op1.toNat - l.dist.toNat)) :=
            subn_ok (r := e.ob) (a := A1) (e.heap_bytes_ob A1 msg m) (by omega) (by omega)
          refine Wp.bindO hsub2 ?_
          refine Wp.of_eq (a := _) (h' := _) (tailW_run (Src.out e) A1 msg m
            { l with out := Ptr.ref e.ob (o + op1.toNat), op := 0, len := l.len - op1,
                     from_ := Ptr.ref e.ob (o + op1.toNat - l.dist.toNat) }
            (l.len - op1).toNat (o + op1.toNat - l.dist.toNat) (o + op1.toNat) rfl rfl rfl (by simp; omega)
            (by omega)) ?_
          refine ⟨rfl, rfl, rfl, rfl, rfl, Or.inl ⟨hbroke, ?_, ?_⟩⟩
          · simp only [hlen1]; rw [show o + op1.toNat + (l.len.toNat - op1.toNat) = o + l.len.toNat by omega]
          · simp only [hlen1]
            rw [cpyG_id]
            unfold matchArr
            have h1 : o - e.bg < l.dist.toNat := by omega
            have h2 : e.s0.wnext.toNat = 0 := by rw [← hwnx]; rw [hn0]; rfl
            simp only [h1, h2, ite_true]
            have h3 : op1.toNat = l.dist.toNat - (o - e.bg) := hop1
            have h4 : op1.toNat < l.len.toNat := by omega
            have h4' : l.dist.toNat - (o - e.bg) < l.len.toNat := by omega
            have h5 : e.woff + (c.wsize.toNat - (l.dist.toNat - (o - e.bg))) =
                e.woff + e.s0.wsize.toNat - (l.dist.toNat - (o - e.bg)) := by omega
            simp only [h3, h4'] at hA1 ⊢
            rw [h5] at hA1
            rw [← hA1]
            try simp
        · simp only [hlt, ite_false]
          have hlt' : l.len.toNat ≤ op1.toNat := by
            have h1 : ¬ (op1 < l.len) := hlt
            have h2 : ¬ (op1.toNat < l.len.toNat) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr h)
            omega
          refine Wp.of_eq (a := _) (h' := _) (tailW_run hsrc A msg m
            { l with op := op1, from_ := Ptr.ref (BRef.blk e.wb) (e.woff + (c.wsize.toNat - (l.dist.toNat - (o - e.bg)))) }
            l.len.toNat (e.woff + (c.wsize.toNat - (l.dist.toNat - (o - e.bg)))) o rfl rfl hout
            (by show _ ≤ e.W.size; omega) (by omega)) ?_
          refine ⟨rfl, rfl, rfl, rfl, rfl, Or.inl ⟨hbroke, rfl, ?_⟩⟩
          rw [cpyG_const]
          unfold matchArr
          have h1 : o - e.bg < l.dist.toNat := by omega
          have h2 : e.s0.wnext.toNat = 0 := by rw [← hwnx]; rw [hn0]; rfl
          have h3 : op1.toNat = l.dist.toNat - (o - e.bg) := hop1
          have h4' : ¬ (l.dist.toNat - (o - e.bg) < l.len.toNat) := by omega
          have h5 : e.woff + (c.wsize.toNat - (l.dist.toNat - (o - e.bg))) =
              e.woff + e.s0.wsize.toNat - (l.dist.toNat - (o - e.bg)) := by omega
          simp only [h1, h2, h4', ite_true, ite_false, h5]
      · -- the window has wrapped (ii) or the data is contiguous (iii)
        have hn0' : (c.wnext == 0) = false := by simp [hn0]
        simp only [hn0']
        have hn0n : 0 < c.wnext.toNat := by
          have : c.wnext.toNat ≠ 0 := fun h => hn0 (UInt32.toNat_inj.mp (by simpa using h))
          omega
        by_cases hwl : c.wnext < l.dist - l.op
        · -- (ii)
          simp only [hwl, ite_true]
          have hwl' : c.wnext.toNat < (l.dist - l.op).toNat := UInt32.lt_iff_toNat_lt.mp hwl
          have hsum : (c.wsize + c.wnext).toNat = c.wsize.toNat + c.wnext.toNat := u32_toNat_add (by omega)
          have hsubw : (c.wsize + c.wnext - (l.dist - l.op)).toNat =
              c.wsize.toNat + c.wnext.toNat - (l.dist.toNat - (o - e.bg)) := by
            rw [u32_toNat_sub (by omega), hsum, hop1]
          have hadd : OkOn (e.heap A msg m) (Ptr.add c.window ↑(c.wsize + c.wnext - (l.dist - l.op)).toNat)
              (Ptr.ref (BRef.blk e.wb) (e.woff + (c.wsize.toNat + c.wnext.toNat - (l.dist.toNat - (o - e.bg))))) := by
            rw [hwptr', hsubw]
            exact Ptr.add_nat_ok hWg (by omega)
          refine Wp.bindO hadd ?_
          generalize l.dist - l.op = op1 at hop1 hw' hadd hwl' ⊢
          have hop2 : (op1 - c.wnext).toNat = op1.toNat - c.wnext.toNat := u32_toNat_sub (by omega)
          generalize op1 - c.wnext = op2 at hop2 ⊢
          have hfo1 : e.woff + (c.wsize.toNat + c.wnext.toNat - (l.dist.toNat - (o - e.bg))) =
              e.woff + e.s0.wsize.toNat + e.s0.wnext.toNat - (l.dist.toNat - (o - e.bg)) := by omega
          by_cases hlt : op2 < l.len
          · simp only [hlt, ite_true]
            have hlt' : op2.toNat < l.len.toNat := UInt32.lt_iff_toNat_lt.mp hlt
            have hlen1 : (l.len - op2).toNat = l.len.toNat - op2.toNat := u32_toNat_sub (by omega)
            refine Wp.bindE (copyOp_win e e.W msg m (BRef.blk e.wb) hwb hWb A
              { l with op := op2, len := l.len - op2, from_ := Ptr.ref (BRef.blk e.wb) (e.woff + (c.wsize.toNat + c.wnext.toNat - (l.dist.toNat - (o - e.bg)))) }
              op2.toNat (e.woff + (c.wsize.toNat + c.wnext.toNat - (l.dist.toNat - (o - e.bg)))) o rfl (by omega) rfl hout
              (by omega) (by omega)) ?_
            dsimp only
            generalize hA1 : blitN e.W op2.toNat (e.woff + (c.wsize.toNat + c.wnext.toNat - (l.dist.toNat - (o - e.bg)))) o A = A1
            have hA1sz : A1.size = A.size := by rw [← hA1]; exact blitN_size _ _ _ _ _
            by_cases hwl2 : c.wnext < l.len - op2
            · simp only [hwl2, ite_true]
              have hwl2' : c.wnext.toNat < (l.len - op2).toNat := UInt32.lt_iff_toNat_lt.mp hwl2
              have hlen2 : (l.len - op2 - c.wnext).toNat = l.len.toNat - op2.toNat - c.wnext.toNat := by
                rw [u32_toNat_sub (by omega), hlen1]
              refine Wp.bindE (copyOp_win e e.W msg m (BRef.blk e.wb) hwb hWb A1
                { l with out := Ptr.ref e.ob (o + op2.toNat), op := c.wnext, len := l.len - op2 - c.wnext,
                         from_ := c.window }
                c.wnext.toNat e.woff (o + op2.toNat) rfl hn0n hwptr' rfl (by omega) (by omega)) ?_
              dsimp only
              generalize hA2 : blitN e.W c.wnext.toNat e.woff (o + op2.toNat) A1 = A2
              have hA2sz : A2.size = A.size := by rw [← hA2]; rw [blitN_size]; exact hA1sz
              have hsub2 : OkOn (e.heap A2 msg m) (subn (Ptr.ref e.ob (o + op2.toNat + c.wnext.toNat)) l.dist)
                  (Ptr.ref e.ob (o + op2.toNat + c.wnext.toNat - l.dist.toNat)) :=
                subn_ok (r := e.ob) (a := A2) (e.heap_bytes_ob A2 msg m) (by omega) (by omega)
              refine Wp.bindO hsub2 ?_
              refine Wp.of_eq (a := _) (h' := _) (tailW_run (Src.out e) A2 msg m
                { l with out := Ptr.ref e.ob (o + op2.toNat + c.wnext.toNat), op := 0,
                         len := l.len - op2 - c.wnext,
                         from_ := Ptr.ref e.ob (o + op2.toNat + c.wnext.toNat - l.dist.toNat) }
                (l.len - op2 - c.wnext).toNat (o + op2.toNat + c.wnext.toNat - l.dist.toNat)
                (o + op2.toNat + c.wnext.toNat) rfl rfl rfl (by simp; omega) (by omega)) ?_
              refine ⟨rfl, rfl, rfl, rfl, rfl, Or.inl ⟨hbroke, ?_, ?_⟩⟩
              · simp only [hlen2]; rw [show o + op2.toNat + c.wnext.toNat + (l.len.toNat - op2.toNat - c.wnext.toNat) = o + l.len.toNat by omega]
              · simp only [hlen2]
                rw [cpyG_id]
                unfold matchArr
                have h1 : o - e.bg < l.dist.toNat := by omega
                have h2 : ¬ (e.s0.wnext.toNat = 0) := by rw [← hwnx]; omega
                have h3 : e.s0.wnext.toNat < l.dist.toNat - (o - e.bg) := by rw [← hwnx]; omega
                have h4 : l.dist.toNat - (o - e.bg) - e.s0.wnext.toNat < l.len.toNat := by rw [← hwnx]; omega
                have h5 : e.s0.wnext.toNat < l.len.toNat - (l.dist.toNat - (o - e.bg) - e.s0.wnext.toNat) := by
                  rw [← hwnx]; omega
                simp only [h1, h2, h3, h4, h5, ite_true, ite_false]
                rw [← hA2, ← hA1, hfo1]
                have hop2' : op2.toNat = l.dist.toNat - (o - e.bg) - e.s0.wnext.toNat := by omega
                simp only [hop2', hwnx]
            · simp only [hwl2, ite_false]
              have hwl2' : (l.len - op2).toNat ≤ c.wnext.toNat := by
                have h1 : ¬ (c.wnext < l.len - op2) := hwl2
                have h2 : ¬ (c.wnext.toNat < (l.len - op2).toNat) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr h)
                omega
              refine Wp.of_eq (a := _) (h' := _) (tailW_run hsrc A1 msg m
                { l with out := Ptr.ref e.ob (o + op2.toNat), op := 0, len := l.len - op2, from_ := c.window }
                (l.len - op2).toNat e.woff (o + op2.toNat) rfl hwptr' rfl (by show _ ≤ e.W.size; omega) (by omega)) ?_
              refine ⟨rfl, rfl, rfl, rfl, rfl, Or.inl ⟨hbroke, ?_, ?_⟩⟩
              · simp only [hlen1]; rw [show o + op2.toNat + (l.len.toNat - op2.toNat) = o + l.len.toNat by omega]
              · simp only [hlen1]
                rw [cpyG_const]
                unfold matchArr
                have h1 : o - e.bg < l.dist.toNat := by omega
                have h2 : ¬ (e.s0.wnext.toNat = 0) := by rw [← hwnx]; omega
                have h3 : e.s0.wnext.toNat < l.dist.toNat - (o - e.bg) := by rw [← hwnx]; omega
                have h4 : l.dist.toNat - (o - e.bg) - e.s0.wnext.toNat < l.len.toNat := by rw [← hwnx]; omega
                have h5 : ¬ (e.s0.wnext.toNat < l.len.toNat - (l.dist.toNat - (o - e.bg) - e.s0.wnext.toNat)) := by
                  rw [← hwnx]; omega
                simp only [h1, h2, h3, h4, h5, ite_true, ite_false]
                rw [← hA1, hfo1]
                have hop2' : op2.toNat = l.dist.toNat - (o - e.bg) - e.s0.wnext.toNat := by omega
                simp only [hop2']
          · simp only [hlt, ite_false]
            have hlt' : l.len.toNat ≤ op2.toNat := by
              have h1 : ¬ (op2 < l.len) := hlt
              have h2 : ¬ (op2.toNat < l.len.toNat) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr h)
              omega
            refine Wp.of_eq (a := _) (h' := _) (tailW_run hsrc A msg m
              { l with op := op2, from_ := Ptr.ref (BRef.blk e.wb) (e.woff + (c.wsize.toNat + c.wnext.toNat - (l.dist.toNat - (o - e.bg)))) }
              l.len.toNat (e.woff + (c.wsize.toNat + c.wnext.toNat - (l.dist.toNat - (o - e.bg)))) o rfl rfl hout
              (by show _ ≤ e.W.size; omega) (by omega)) ?_
            refine ⟨rfl, rfl, rfl, rfl, rfl, Or.inl ⟨hbroke, rfl, ?_⟩⟩
            rw [cpyG_const]
            unfold matchArr
            have h1 : o - e.bg < l.dist.toNat := by omega
            have h2 : ¬ (e.s0.wnext.toNat = 0) := by rw [← hwnx]; omega
            have h3 : e.s0.wnext.toNat < l.dist.toNat - (o - e.bg) := by rw [← hwnx]; omega
            have h4 : ¬ (l.dist.toNat - (o - e.bg) - e.s0.wnext.toNat < l.len.toNat) := by rw [← hwnx]; omega
            simp only [h1, h2, h3, h4, ite_true, ite_false]
            rw [hfo1]
        · -- (iii)
          simp only [hwl, ite_false]
          have hwl' : (l.dist - l.op).toNat ≤ c.wnext.toNat := by
            have h2 : ¬ (c.wnext.toNat < (l.dist - l.op).toNat) := fun h => hwl (UInt32.lt_iff_toNat_lt.mpr h)
            omega
          have hsubw : (c.wnext - (l.dist - l.op)).toNat = c.wnext.toNat - (l.dist.toNat - (o - e.bg)) := by
            rw [u32_toNat_sub (by omega), hop1]
          have hadd : OkOn (e.heap A msg m) (Ptr.add c.window ↑(c.wnext - (l.dist - l.op)).toNat)
              (Ptr.ref (BRef.blk e.wb) (e.woff + (c.wnext.toNat - (l.dist.toNat - (o - e.bg))))) := by
            rw [hwptr', hsubw]
            exact Ptr.add_nat_ok hWg (by omega)
          refine Wp.bindO hadd ?_
          generalize l.dist - l.op = op1 at hop1 hw' hadd hwl' ⊢
          by_cases hlt : op1 < l.len
          · simp only [hlt, ite_true]
            have hlt' : op1.toNat < l.len.toNat := UInt32.lt_iff_toNat_lt.mp hlt
            have hlen1 : (l.len - op1).toNat = l.len.toNat - op1.toNat := u32_toNat_sub (by omega)
            refine Wp.bindE (copyOp_win e e.W msg m (BRef.blk e.wb) hwb hWb A
              { l with op := op1, len := l.len - op1, from_ := Ptr.ref (BRef.blk e.wb) (e.woff + (c.wnext.toNat - (l.dist.toNat - (o - e.bg)))) }
              op1.toNat (e.woff + (c.wnext.toNat - (l.dist.toNat - (o - e.bg)))) o rfl (by omega) rfl hout
              (by omega) (by omega)) ?_
            dsimp only
            generalize hA1 : blitN e.W op1.toNat (e.woff + (c.wnext.toNat - (l.dist.toNat - (o - e.bg)))) o A = A1
            have hA1sz : A1.size = A.size := by rw [← hA1]; exact blitN_size _ _ _ _ _
            have hsub2 : OkOn (e.heap A1 msg m) (subn (Ptr.ref e.ob (o + op1.toNat)) l.dist)
                (Ptr.ref e.ob (o + op1.toNat - l.dist.toNat)) :=
              subn_ok (r := e.ob) (a := A1) (e.heap_bytes_ob A1 msg m) (by omega) (by omega)
            refine Wp.bindO hsub2 ?_
            refine Wp.of_eq (a := _) (h' := _) (tailW_run (Src.out e) A1 msg m
              { l with out := Ptr.ref e.ob (o + op1.toNat), op := 0, len := l.len - op1,
                       from_ := Ptr.ref e.ob (o + op1.toNat - l.dist.toNat) }
              (l.len - op1).toNat (o + op1.toNat - l.dist.toNat) (o + op1.toNat) rfl rfl rfl (by simp; omega)
              (by omega)) ?_
            refine ⟨rfl, rfl, rfl, rfl, rfl, Or.inl ⟨hbroke, ?_, ?_⟩⟩
            · simp only [hlen1]; rw [show o + op1.toNat + (l.len.toNat - op1.toNat) = o + l.len.toNat by omega]
            · simp only [hlen1]
              rw [cpyG_id]
              unfold matchArr
              have h1 : o - e.bg < l.dist.toNat := by omega
              have h2 : ¬ (e.s0.wnext.toNat < l.dist.toNat - (o - e.bg)) := by rw [← hwnx]; omega
              have h3 : op1.toNat = l.dist.toNat - (o - e.bg) := hop1
              have h4' : l.dist.toNat - (o - e.bg) < l.len.toNat := by omega
              have h5 : e.woff + (c.wnext.toNat - (l.dist.toNat - (o - e.bg))) =
                  e.woff + e.s0.wnext.toNat - (l.dist.toNat - (o - e.bg)) := by omega
              have h6 : ¬ (e.s0.wnext.toNat = 0) := by rw [← hwnx]; omega
              simp only [h1, h2, h3, h4', h6, ite_true, ite_false] at hA1 ⊢
              rw [h5] at hA1
              rw [← hA1]
          · simp only [hlt, ite_false]
            have hlt' : l.len.toNat ≤ op1.toNat := by
              have h1 : ¬ (op1 < l.len) := hlt
              have h2 : ¬ (op1.toNat < l.len.toNat) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr h)
              omega
            refine Wp.of_eq (a := _) (h' := _) (tailW_run hsrc A msg m
              { l with op := op1, from_ := Ptr.ref (BRef.blk e.wb) (e.woff + (c.wnext.toNat - (l.dist.toNat - (o - e.bg)))) }
              l.len.toNat (e.woff + (c.wnext.toNat - (l.dist.toNat - (o - e.bg)))) o rfl rfl hout
              (by show _ ≤ e.W.size; omega) (by omega)) ?_
            refine ⟨rfl, rfl, rfl, rfl, rfl, Or.inl ⟨hbroke, rfl, ?_⟩⟩
            rw [cpyG_const]
            unfold matchArr
            have h1 : o - e.bg < l.dist.toNat := by omega
            have h2 : ¬ (e.s0.wnext.toNat < l.dist.toNat - (o - e.bg)) := by rw [← hwnx]; omega
            have h4' : ¬ (l.dist.toNat - (o - e.bg) < l.len.toNat) := by omega
            have h5 : e.woff + (c.wnext.toNat - (l.dist.toNat - (o - e.bg))) =
                e.woff + e.s0.wnext.toNat - (l.dist.toNat - (o - e.bg)) := by omega
            have h6 : ¬ (e.s0.wnext.toNat = 0) := by rw [← hwnx]; omega
            simp only [h1, h2, h4', h6, ite_true, ite_false, h5]
  · simp only [hd, ite_false]
    have hd' : l.dist.toNat ≤ o - e.bg := by
      have h1 : ¬ (l.op < l.dist) := hd
      have h2 : ¬ (l.op.toNat < l.dist.toNat) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr h)
      omega
    have hsub : OkOn (e.heap A msg m) (subn l.out l.dist) (Ptr.ref e.ob (o - l.dist.toNat)) := by
      rw [hout]; exact subn_ok (r := e.ob) (a := A) (e.heap_bytes_ob A msg m) (by omega) hoA
    refine Wp.bindO hsub ?_
    refine Wp.of_eq (a := _) (h' := _) (tailD_run (Src.out e) A msg m
      { l with from_ := Ptr.ref e.ob (o - l.dist.toNat) } l.len.toNat (o - l.dist.toNat) o rfl hlen rfl hout
      (by simp; omega) (by omega)) ?_
    have hmb : ¬ (o - e.bg < l.dist.toNat) := by omega
    refine ⟨rfl, rfl, rfl, rfl, rfl, Or.inl ⟨hbroke, rfl, ?_⟩⟩
    rw [e.mArr_near hmb, cpyG_id]

end Zlib.Inffast.Proofs
