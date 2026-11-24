import ZlibF.Proof.«inftrees.c.decoder-safe»
import ZlibF.Spec.Safety.StandaloneCAbi
import ZlibF.Proof.HeapWP
import ZlibF.Proof.«inftrees.c.abi-step»

/-! Relate the exact C-shaped decoder table builder to the loops used by its
safety proof. The C-shaped loops carry their locals in a single record. -/

namespace Zlib.Inftrees.TableABI
open C Zlib.Inftrees.Proofs

private abbrev Count := Array UInt16
private abbrev Locals := InflateTableLocals

private def clearBody : Locals × Count → M (Locals × Count) := fun (l, count) => do
  pure ({l with len := l.len + 1}, ← seta count l.len.toNat 0)

private def histogramBody (lens : WPtr) : Locals × Count → M (Locals × Count) := fun (l, count) => do
  let a ← cinline (lens.index l.sym.toNat)
  let c ← cinline (geta count a.toNat)
  let b ← cinline (lens.index l.sym.toNat)
  pure ({l with sym := l.sym + 1}, ← seta count b.toNat (c + 1))

private theorem clear_sim (l : Locals) (x : UInt32 × Count) :
    Sim (fun r : UInt32 × Count => ({l with len := r.1}, r.2))
      (cwhile zeroCond zeroBody x)
      (cwhile (fun (s, count) => pure (s.len ≤ MAXBITS, (s, count))) clearBody ({l with len := x.1}, x.2)) := by
  refine @while_sim (UInt32 × Count) (Locals × Count) (fun r => ({l with len := r.1}, r.2))
    (fun r => decide (r.1 ≤ MAXBITS)) zeroCond (fun (t, a) => pure (t.len ≤ MAXBITS, (t, a)))
    zeroBody clearBody ?_ ?_ x
  · rintro ⟨_, _⟩ _; exact ⟨rfl, rfl⟩
  rintro ⟨ix, count⟩ h s H run
  simp only [zeroBody, clearBody, bind_app, pure_app] at run ⊢
  cases store : seta count ix.toNat 0 h with
  | error fault => simp [store] at run
  | ok pair => rcases pair with ⟨a, mid⟩; rw [store] at run; cases run; rfl

private theorem histogram_sim (l : Locals) (lens : WPtr) (codes : UInt32) (x : UInt32 × Count) :
    Sim (fun r : UInt32 × Count => ({l with sym := r.1}, r.2))
      (cwhile (countCond codes) (countBody lens) x)
      (cwhile (fun (s, count) => pure (s.sym < codes, (s, count))) (histogramBody lens)
        ({l with sym := x.1}, x.2)) := by
  refine @while_sim (UInt32 × Count) (Locals × Count) (fun r => ({l with sym := r.1}, r.2))
    (fun r => decide (r.1 < codes)) (countCond codes) (fun (t, a) => pure (t.sym < codes, (t, a)))
    (countBody lens) (histogramBody lens) ?_ ?_ x
  · rintro ⟨_, _⟩ _; exact ⟨rfl, rfl⟩
  rintro ⟨ix, count⟩ h s H run
  simp only [countBody, histogramBody, cinline_eq, bind_app, pure_app] at run ⊢
  cases load : lens.index (ix.toNat : Int) h with
  | error fault => simp [load] at run
  | ok pair =>
    obtain ⟨width, mid⟩ := pair
    obtain rfl := Ptr.index_heap load
    simp only [load] at run ⊢
    unfold geta at run ⊢
    cases entry : count[width.toNat]? with
    | none => simp [entry, ub] at run
    | some n =>
      simp only [entry, pure_app, load] at run ⊢
      cases store : seta count width.toNat (n+1) mid with
      | error fault => simp [store] at run
      | ok pair => obtain ⟨a, final⟩ := pair; rw [store] at run; cases run; rfl

/-- The old scan carries an extra Boolean to simulate C's immediate break.
A successful old run has enough fuel for that extra test. -/
private theorem scan_sim (embed : UInt32 → Locals) (test : UInt32 → Bool) (move : UInt32 → UInt32)
    (count : Count) (guard : Locals → M (Bool × Locals))
    (body : Locals → M (LoopStep Locals Empty))
    (gc : ∀ i h, guard (embed i) h = .ok ((test i, embed i), h))
    (bc : ∀ i h,
      body (embed i) h = (do
        if (← geta count i.toNat) != 0 then pure (.brk (embed i))
        else pure (.next (embed (move i))) : M (LoopStep Locals Empty)) h)
    (start : UInt32) :
    Sim (fun p : UInt32 × Bool => embed p.1)
      (cwhile (fun (i, stop) => pure (!stop && test i, (i, stop)))
        (fun (i, stop) => do if (← geta count i.toNat) != 0 then pure (i, true) else pure (move i, stop))
        (start, false))
      (cwhileBrk guard body (embed start)) := by
  let c₀ : UInt32 × Bool → M (Bool × (UInt32 × Bool)) :=
    fun (i, stop) => pure (!stop && test i, (i, stop))
  let b₀ : UInt32 × Bool → M (UInt32 × Bool) :=
    fun (i, stop) => do if (← geta count i.toNat) != 0 then pure (i, true) else pure (move i, stop)
  have loop (n : Nat) (i : UInt32) {h result H}
      (run : cwhile.go c₀ b₀ n (i, false) h = .ok (result, H)) :
      cwhileCtrl.go guard body n (embed i) h = .ok (.ok (embed result.1), H) := by
    induction n generalizing i h with
    | zero => cases run
    | succ n ih =>
      rw [cwhile.go, bind_app] at run
      rw [cwhileCtrl.go, bind_ok (gc i h)]
      simp only [c₀, pure_app, Bool.not_false, Bool.true_and] at run
      cases t : test i <;> simp only [t, Bool.false_eq_true, ↓reduceIte] at run ⊢
      · cases run; rfl
      · rw [bind_app] at run ⊢
        simp only [b₀, bc, bind_app] at run ⊢
        cases g : geta count i.toNat h with
        | error fault => simp [g] at run
        | ok p =>
          obtain ⟨v, mid⟩ := p
          cases z : v != 0 <;> simp only [g, z, Bool.false_eq_true, ↓reduceIte, pure_app] at run ⊢
          · exact ih _ run
          · cases n with
            | zero => cases run
            | succ n =>
              rw [cwhile.go, bind_app] at run
              simp only [pure_app, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at run
              cases run; rfl
  intro h s H run
  unfold cwhileBrk cwhileCtrl
  rw [bind_ok (loop fuel start run)]
  rfl

private def maxGuard (s : Locals) : M (Bool × Locals) := pure (s.max ≥ 1, s)
private def maxStep (count : Count) (s : Locals) : M (LoopStep Locals Empty) := do
  if (← cinline (geta count s.max.toNat)) != 0 then return .brk s
  else return .next {s with max := s.max - 1}

private theorem max_sim (l : Locals) (count : Count) :
    Sim (fun p : UInt32 × Bool => {l with max := p.1})
      (cwhile maxCond (maxBody count) (MAXBITS, false))
      (cwhileBrk maxGuard (maxStep count) {l with max := MAXBITS}) := by
  exact scan_sim (fun i => {l with max := i}) (fun i => decide (i ≥ 1)) (· - 1)
    count maxGuard (maxStep count) (fun _ _ => rfl) (fun _ _ => rfl) MAXBITS

private def minGuard (s : Locals) : M (Bool × Locals) := pure (s.min < s.max, s)
private def minStep (count : Count) (s : Locals) : M (LoopStep Locals Empty) := do
  if (← cinline (geta count s.min.toNat)) != 0 then return .brk s
  else return .next {s with min := s.min + 1}

private theorem min_sim (l : Locals) (count : Count) :
    Sim (fun p : UInt32 × Bool => {l with min := p.1})
      (cwhile (minCond l.max) (minBody count) (1, false))
      (cwhileBrk minGuard (minStep count) {l with min := 1}) := by
  exact scan_sim (fun i => {l with min := i}) (fun i => decide (i < l.max)) (· + 1)
    count minGuard (minStep count) (fun _ _ => rfl) (fun _ _ => rfl) 1

private abbrev Ret := Int32 × CodePtr × UInt32
private abbrev Kraft := Int32 × Bool × UInt32

private def kraftGuard (s : Locals) : M (Bool × Locals) := pure (s.len ≤ MAXBITS, s)
private def kraftStep (count : Count) (reject : Ret) (s : Locals) : M (LoopStep Locals Ret) := do
  if s.left < (0 : Int32) then ub "left shift of a negative value" else
    let first ← cinline (chk32 (s.left.toInt * 2))
    let t := {s with left := first}
    let cc ← cinline (geta count t.len.toNat)
    let next ← cinline (chk32 (t.left.toInt - cc.toNat))
    let u := {t with left := next}
    if u.left < (0 : Int32) then return .ret reject
    return .next {u with len := u.len + 1}

private def kraftLocals (l : Locals) (left : Int32) (len : UInt32) : Locals := {l with left, len}

private theorem kraft_step_sim (count : Count) (l : Locals) (reject : Ret) (left : Int32) (len : UInt32) :
    Sim (fun s : Kraft => if s.2.1 then .ret reject else .next (kraftLocals l s.1 s.2.2))
      (kraftBody count (left, false, len)) (kraftStep count reject (kraftLocals l left len)) := by
  intro h s H run
  simp only [kraftBody, kraftStep, kraftLocals, cinline_eq] at run ⊢
  by_cases neg : left < 0
  · simp only [neg, ↓reduceIte, ub, reduceCtorEq] at run
  simp only [neg, ↓reduceIte, bind_app] at run ⊢
  cases f : chk32 (left.toInt * 2) h with
  | error fault => simp [f] at run
  | ok p =>
    obtain ⟨first, mid⟩ := p
    simp only [f] at run ⊢
    cases g : geta count len.toNat mid with
    | error fault => simp [g] at run
    | ok p =>
      obtain ⟨cc, after⟩ := p
      simp only [g] at run ⊢
      cases last : chk32 (first.toInt - cc.toNat) after with
      | error fault => simp [last] at run
      | ok p =>
        obtain ⟨v, final⟩ := p
        by_cases bad : v < 0 <;> simp only [last, bad, ↓reduceIte, pure_app] at run ⊢ <;> cases run <;> rfl

private theorem kraft_sim (l : Locals) (count : Count) (reject : Ret) :
    Sim (fun s : Kraft => if s.2.1 then .error reject else .ok (kraftLocals l s.1 s.2.2))
      (cwhile kraftCond (kraftBody count) (1, false, 1))
      (cwhileCtrl kraftGuard (kraftStep count reject) (kraftLocals l 1 1)) := by
  have loop (n : Nat) (left : Int32) (len : UInt32) {h s H}
      (run : cwhile.go kraftCond (kraftBody count) n (left, false, len) h = .ok (s, H)) :
      cwhileCtrl.go kraftGuard (kraftStep count reject) n (kraftLocals l left len) h =
        .ok ((if s.2.1 then .error reject else .ok (kraftLocals l s.1 s.2.2)), H) := by
    induction n generalizing left len h with
    | zero => cases run
    | succ n ih =>
      rw [cwhile.go, bind_app] at run
      rw [cwhileCtrl.go, bind_app]
      simp only [kraftCond, kraftGuard, kraftLocals, pure_app, Bool.not_false, Bool.true_and] at run ⊢
      by_cases cont : len ≤ MAXBITS <;> simp only [cont, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] at run ⊢
      case neg => cases run; rfl
      rw [bind_app] at run ⊢
      cases step : kraftBody count (left, false, len) h with
      | error fault => simp [step] at run
      | ok p =>
        obtain ⟨⟨v, bad, ix⟩, mid⟩ := p
        have lifted := kraft_step_sim count l reject left len step
        simp only [step] at run
        cases bad <;> simp only [kraftLocals, Bool.false_eq_true, ↓reduceIte] at lifted
        · rw [lifted]
          exact ih v ix run
        · rw [lifted]
          cases n with
          | zero => cases run
          | succ n =>
            rw [cwhile.go, bind_app] at run
            simp only [kraftCond, pure_app, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at run
            cases run; rfl
  intro h s H run
  exact loop fuel 1 1 run

private def offsetsBody (count : Count) : Locals × Count → M (Locals × Count) := fun (s, offs) => do
  let a ← cinline (geta offs s.len.toNat)
  let b ← cinline (geta count s.len.toNat)
  pure ({s with len := s.len + 1}, ← seta offs (s.len + 1).toNat (a + b))

private theorem offsets_sim (l : Locals) (count : Count) (x : UInt32 × Count) :
    Sim (fun r : UInt32 × Count => ({l with len := r.1}, r.2))
      (cwhile offsCond (offsBody count) x)
      (cwhile (fun (s, offs) => pure (s.len < MAXBITS, (s, offs))) (offsetsBody count)
        ({l with len := x.1}, x.2)) := by
  refine @while_sim (UInt32 × Count) (Locals × Count) (fun r => ({l with len := r.1}, r.2))
    (fun r => decide (r.1 < MAXBITS)) offsCond (fun (s, a) => pure (s.len < MAXBITS, (s, a)))
    (offsBody count) (offsetsBody count) ?_ ?_ x
  · rintro ⟨_, _⟩ _; exact ⟨rfl, rfl⟩
  rintro ⟨ix, a⟩ h r H run
  unfold offsetsBody
  unfold offsBody at run
  iterate 3 (apply sameBind run; intro val mid run)
  cases run; rfl

private def orderBody (lens work : WPtr) : Locals × Count → M (Locals × Count) := fun (s, offs) => do
  let lv ← cinline (lens.index s.sym.toNat)
  let offs' ← if lv != 0 then
      let lv2 ← cinline (lens.index s.sym.toNat)
      storeAtPostInc work offs lv2.toNat s.sym.toUInt16
    else pure offs
  pure ({s with sym := s.sym + 1}, offs')

private theorem order_sim (l : Locals) (lens work : WPtr) (codes : UInt32) (x : UInt32 × Count) :
    Sim (fun r : UInt32 × Count => ({l with sym := r.1}, r.2))
      (cwhile (sortCond codes) (sortBody lens work) x)
      (cwhile (fun (s, offs) => pure (s.sym < codes, (s, offs))) (orderBody lens work)
        ({l with sym := x.1}, x.2)) := by
  refine @while_sim (UInt32 × Count) (Locals × Count) (fun r => ({l with sym := r.1}, r.2))
    (fun r => decide (r.1 < codes)) (sortCond codes) (fun (s, a) => pure (s.sym < codes, (s, a)))
    (sortBody lens work) (orderBody lens work) ?_ ?_ x
  · rintro ⟨_, _⟩ _; exact ⟨rfl, rfl⟩
  rintro ⟨ix, offs⟩ h r H run
  unfold orderBody
  unfold sortBody at run
  apply sameBind run
  intro lv h run
  cases test : lv != 0 <;> simp only [test, Bool.false_eq_true, ↓reduceIte, M_pure_bind] at run ⊢
  · cases run; rfl
  apply sameBind run
  intro width mid run
  by_cases inside : width.toNat < offs.size
  · rw [geta_eq inside, M_pure_bind, seta_eq inside, M_pure_bind] at run
    simp only [storeAtPostInc, Array.getElem?_eq_getElem inside, bind_assoc_table, M_pure_bind]
    iterate 2 (apply sameBind run; intro val mid run)
    cases run; rfl
  · unfold geta at run
    simp only [Array.getElem?_eq_none (by omega : offs.size ≤ width.toNat), bind_app, ub, reduceCtorEq] at run

private def initial : Locals :=
  ⟨default, default, default, default, default, default, default, default, default, default,
   default, default, default, default, default, default, #[], #[], 0⟩

private theorem two_invalid (table : CodePtr) (h : Heap) :
    (do let next ← storePostIncCode table ⟨64, 1, 0⟩
        let final ← storePostIncCode next ⟨64, 1, 0⟩
        pure ((0 : Int32), final, (1 : UInt32)) : M _) h =
    (do Ptr.store table ⟨64, 1, 0⟩
        let next ← table.add 1
        Ptr.store next ⟨64, 1, 0⟩
        let final ← next.add 1
        pure ((0 : Int32), final, (1 : UInt32)) : M _) h := by
  simp only [storePostIncCode, bind_assoc_table]

private def build (type : UInt32) (lens : WPtr) (table : CodePtr) (bits : UInt32) (work : WPtr)
    (count : Count) (s : Locals) : M Ret := do
  let used ← cinline (shl32 1 s.root)
  let s := {s with
    huff := 0, sym := 0, len := s.min, next := table, curr := s.root, drop := 0,
    low := 0xffffffff, used}
  let s := {s with mask := s.used - 1}
  if tooBig type s.used then return (1, table, bits)
  let c : Ctx := ⟨type,lens,work,table,s.root,s.max,s.base,s.extra,s.match_⟩
  cforEverRet (tableStep c bits) (s,count) (finishTable table)

private def selectKind (type : UInt32) (lens : WPtr) (table : CodePtr) (bits : UInt32) (work : WPtr)
    (count : Count) (s : Locals) : M Ret := do
  let mut s := s
  if type == CODES then s := {s with match_ := 20}
  else if type == LENS then s := {s with base := lbase, extra := lext, match_ := 257}
  else if type == DISTS then s := {s with base := dbase, extra := dext}
  build type lens table bits work count s

private def afterKraft (type : UInt32) (lens : WPtr) (codes : UInt32) (table : CodePtr) (bits : UInt32)
    (work : WPtr) (count : Count) (s : Locals) : M Ret := do
  if s.left > 0 && (type == CODES || s.max != 1) then return (-1, table, bits)
  let offs ← seta (Array.replicate 16 0) 1 0
  let (s, offs) ← cwhile (fun (s, a) => pure (s.len < MAXBITS, (s, a))) (offsetsBody count) ({s with len := 1}, offs)
  let (s, _) ← cwhile (fun (s, a) => pure (s.sym < codes, (s, a))) (orderBody lens work) ({s with sym := 0}, offs)
  selectKind type lens table bits work count s

private def actualB (type : UInt32) (lens : WPtr) (codes : UInt32) (table : CodePtr) (bits : UInt32)
    (work : WPtr) (count : Count) (s : Locals) : M Ret :=
  cwhileRet kraftGuard (kraftStep count (-1, table, bits)) (kraftLocals s 1 1)
    (afterKraft type lens codes table bits work count)

private def actualA (type : UInt32) (lens : WPtr) (codes : UInt32) (table : CodePtr) (bits : UInt32)
    (work : WPtr) (count : Count) (s : Locals) : M Ret := do
  if s.max == 0 then
    let here : Code := ⟨64, 1, 0⟩
    let table ← storePostIncCode table here
    let table ← storePostIncCode table here
    return (0, table, 1)
  let mut s ← cwhileBrk minGuard (minStep count) {s with min := 1}
  if s.root < s.min then s := {s with root := s.min}
  actualB type lens codes table bits work count s

private def actualTop (type : UInt32) (lens : WPtr) (codes : UInt32) (table : CodePtr) (bits : UInt32)
    (work : WPtr) : M Ret := do
  let l ← cdecl initial
  let (l, count) ← cwhile (fun (s, a) => pure (s.len ≤ MAXBITS, (s, a))) clearBody
    ({l with len := 0}, Array.replicate 16 0)
  let (l, count) ← cwhile (fun (s, a) => pure (s.sym < codes, (s, a))) (histogramBody lens)
    ({l with sym := 0}, count)
  let mut s ← cwhileBrk maxGuard (maxStep count) {l with root := bits, max := MAXBITS}
  if s.root > s.max then s := {s with root := s.max}
  actualA type lens codes table bits work count s

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The named joins above are definitionally the exact function selected for emission. -/
private theorem actual_top_eq : inflate_table_c = actualTop := rfl

private structure Scratch (l : Locals) : Prop where
  fill : l.fill = 0
  incr : l.incr = 0
  here : l.here = default

private structure InitialScratch (l : Locals) : Prop extends Scratch l where
  base : l.base = #[]
  extra : l.extra = #[]
  match_ : l.match_ = 0

private theorem build_sim (type : UInt32) (lens : WPtr) (table : CodePtr) (bits : UInt32) (work : WPtr)
    (count : Count) (l : Locals) (scratch : Scratch l) :
    Sim id (itTail type lens table bits work count l.max l.min l.root l.left l.base l.extra l.match_)
      (build type lens table bits work count l) := by
  intro h r H run
  unfold itTail at run
  unfold build
  apply sameBind run
  intro used h run
  cases cap : tooBig type used <;> simp only [cap, Bool.false_eq_true, ↓reduceIte] at run ⊢
  case true => exact run
  let c : Ctx := ⟨type,lens,work,table,l.root,l.max,l.base,l.extra,l.match_⟩
  let s : TS := { huff := 0, sym := 0, len := l.min, curr := l.root, drop := 0, low := 0xffffffff, used,
                  min := l.min, fill := 0, incr := 0, mask := used - 1, left := l.left, next := table,
                  here := default, count, exit := 0 }
  have actual := build_loop_sim c bits s rfl run
  simpa only [c, s, locals, scratch.fill, scratch.incr, scratch.here] using actual

private def oldKind (type : UInt32) (lens : WPtr) (table : CodePtr) (bits : UInt32) (work : WPtr)
    (count : Count) (max min root : UInt32) (left : Int32) : M Ret := do
  let mut base : Array UInt16 := #[]
  let mut extra : Array UInt16 := #[]
  let mut match_ : UInt32 := 0
  if type == CODES then
    match_ := 20
  else if type == LENS then
    base := lbase; extra := lext; match_ := 257
  else if type == DISTS then
    base := dbase; extra := dext
  itTail type lens table bits work count max min root left base extra match_

private def oldWork (type : UInt32) (lens : WPtr) (codes : UInt32) (table : CodePtr) (bits : UInt32)
    (work : WPtr) (count : Count) (max min root : UInt32) (left : Int32) : M Ret := do
  let offs : Count := Array.replicate 16 0
  if left > 0 && (type == CODES || max != 1) then return (-1, table, bits)
  let offs ← seta offs 1 0
  let (_, offs) ← cwhile (fun (len, offs) => pure (len < MAXBITS, (len, offs)))
    (fun (len, offs) => do
      let a ← geta offs len.toNat
      let b ← geta count len.toNat
      pure (len + 1, ← seta offs (len + 1).toNat (a + b))) ((1 : UInt32), offs)
  let (_, _offs) ← cwhile (fun (sym, offs) => pure (sym < codes, (sym, offs)))
    (fun (sym, offs) => do
      let l ← lens.index sym.toNat
      if l != 0 then
        let l ← lens.index sym.toNat
        let o ← geta offs l.toNat
        let offs ← seta offs l.toNat (o + 1)
        let q ← work.add o.toNat
        Ptr.store q sym.toUInt16
        pure (sym + 1, offs)
      else pure (sym + 1, offs)) ((0 : UInt32), offs)
  oldKind type lens table bits work count max min root left

private theorem kind_sim (type : UInt32) (lens : WPtr) (table : CodePtr) (bits : UInt32) (work : WPtr)
    (count : Count) (l : Locals) (sc : InitialScratch l) :
    Sim id (oldKind type lens table bits work count l.max l.min l.root l.left)
      (selectKind type lens table bits work count l) := by
  intro h r H run
  unfold oldKind at run
  unfold selectKind
  cases a : type == CODES <;> simp only [a, Bool.false_eq_true, ↓reduceIte] at run ⊢
  case true =>
    apply build_sim type lens table bits work count {l with match_ := 20} ⟨sc.fill, sc.incr, sc.here⟩
    simpa only [sc.base, sc.extra] using run
  cases b : type == LENS <;> simp only [b, Bool.false_eq_true, ↓reduceIte] at run ⊢
  case true =>
    exact build_sim type lens table bits work count {l with base := lbase, extra := lext, match_ := 257}
      ⟨sc.fill, sc.incr, sc.here⟩ run
  cases d : type == DISTS <;> simp only [d, Bool.false_eq_true, ↓reduceIte] at run ⊢
  case true =>
    apply build_sim type lens table bits work count {l with base := dbase, extra := dext} ⟨sc.fill, sc.incr, sc.here⟩
    simpa only [sc.match_] using run
  apply build_sim type lens table bits work count l sc.toScratch
  simpa only [sc.base, sc.extra, sc.match_] using run

private theorem work_sim (type : UInt32) (lens : WPtr) (codes : UInt32) (table : CodePtr) (bits : UInt32)
    (work : WPtr) (count : Count) (l : Locals) (sc : InitialScratch l) :
    Sim id (oldWork type lens codes table bits work count l.max l.min l.root l.left)
      (afterKraft type lens codes table bits work count l) := by
  intro h r H run
  unfold oldWork at run
  unfold afterKraft
  cases bad : (l.left > 0 && (type == CODES || l.max != 1)) <;> simp only [bad, Bool.false_eq_true, ↓reduceIte] at run ⊢
  case true => exact run
  apply sameBind run
  intro offsets h run
  apply relatedBind (offsets_sim l count (1, offsets)) run
  rintro ⟨len, a⟩ h run
  let s := {l with len}
  apply relatedBind (order_sim s lens work codes (0, a)) run
  rintro ⟨sym, _⟩ h run
  exact kind_sim type lens table bits work count {s with sym} ⟨⟨sc.fill, sc.incr, sc.here⟩, sc.base, sc.extra, sc.match_⟩ run

private theorem fromKraft_sim (type : UInt32) (lens : WPtr) (codes : UInt32) (table : CodePtr) (bits : UInt32)
    (work : WPtr) (count : Count) (l : Locals) (sc : InitialScratch l) :
    Sim id (itB type lens codes table bits work count l.max l.min l.root) (actualB type lens codes table bits work count l) := by
  intro h r H run
  unfold itB at run
  unfold actualB cwhileRet
  apply relatedBind (kraft_sim l count (-1,table,bits)) run
  rintro ⟨left, flag, ix⟩ h run
  cases flag <;> simp only [Bool.false_eq_true, ↓reduceIte] at run ⊢
  case true => exact run
  exact work_sim type lens codes table bits work count (kraftLocals l left ix)
    ⟨⟨sc.fill, sc.incr, sc.here⟩, sc.base, sc.extra, sc.match_⟩ run

private theorem fromMax_sim (type : UInt32) (lens : WPtr) (codes : UInt32) (table : CodePtr) (bits : UInt32)
    (work : WPtr) (count : Count) (l : Locals) (sc : InitialScratch l) :
    Sim id (itA type lens codes table bits work count l.max l.root) (actualA type lens codes table bits work count l) := by
  intro h r H run
  unfold itA at run
  unfold actualA
  cases no : l.max == 0 <;> simp only [no, Bool.false_eq_true, ↓reduceIte] at run ⊢
  case true => exact (two_invalid table h).trans run
  apply relatedBind (min_sim l count) run
  rintro ⟨mn, _⟩ h run
  by_cases lo : l.root < mn <;> simp only [lo, ↓reduceIte] at run ⊢
  · exact fromKraft_sim type lens codes table bits work count {l with min := mn, root := mn}
      ⟨⟨sc.fill, sc.incr, sc.here⟩, sc.base, sc.extra, sc.match_⟩ run
  · exact fromKraft_sim type lens codes table bits work count {l with min := mn}
      ⟨⟨sc.fill, sc.incr, sc.here⟩, sc.base, sc.extra, sc.match_⟩ run

/-- Every successful execution of the verified table builder has exactly the
same return, root width, next pointer and heap in the builder selected for C
emission, including the writes made before any capacity error. -/
theorem returning_eq (type : UInt32) (lens : WPtr) (codes : UInt32) (table : CodePtr) (bits : UInt32)
    (work : WPtr) {h r H} (run : inflate_table type lens codes table bits work h = .ok (r,H)) :
    inflate_table_c type lens codes table bits work h = .ok (r,H) := by
  rw [inflate_table_eq] at run
  rw [actual_top_eq]
  unfold itTop at run
  unfold actualTop
  rw [cdecl_eq, M_pure_bind]
  apply relatedBind (clear_sim initial (0, Array.replicate 16 0)) run
  rintro ⟨len, zeros⟩ h run
  let a := {initial with len}
  apply relatedBind (histogram_sim a lens codes (0, zeros)) run
  rintro ⟨sym, count⟩ h run
  let b := {a with sym, root := bits}
  apply relatedBind (max_sim b count) run
  rintro ⟨mx, _⟩ h run
  by_cases upper : bits > mx <;> simp only [a, b, upper, ↓reduceIte] at run ⊢
  · exact fromMax_sim type lens codes table bits work count {b with max := mx, root := mx}
      ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩ run
  · exact fromMax_sim type lens codes table bits work count {b with max := mx}
      ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩ run

#print axioms returning_eq

/-- Complete equality on the caller domain of the decoder-table safety proof. -/
theorem caller_eq {h : Heap} {type : UInt32} {rl : WRef} {ol : Nat} {codes : UInt32}
    {rc : CodeRef} {oc : Nat} {bits : UInt32} {rw : WRef} {ow : Nat}
    (pre : CallPre h type rl ol codes rc oc bits rw ow) :
    inflate_table_c type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow) h =
    inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow) h := by
  obtain ⟨r,H,old,_⟩ := itTop_wp pre
  have original : inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow) h = .ok (r,H) := old
  exact (returning_eq _ _ _ _ _ _ original).trans original.symm

theorem inflate_table_c_decoder_safe : Zlib.Inftrees.Spec.Goal.inflate_table_c_decoder_safe := by
  intro h type rl ol codes rc oc bits rw ow pre
  obtain ⟨r, H, run, frame, tables⟩ := inflate_table_decoder_safe h type rl ol codes rc oc bits rw ow pre
  exact ⟨r, H, returning_eq _ _ _ _ _ _ run, frame, tables⟩

#print axioms caller_eq
#print axioms inflate_table_c_decoder_safe
end Zlib.Inftrees.TableABI
