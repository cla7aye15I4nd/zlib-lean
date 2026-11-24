import ZlibF.Proof.«inftrees.c.abi-loops»
import ZlibF.Proof.«inftrees.c.step»

/-! The body of the exact C-shaped table builder, compared at the joins used
by the proof of the Huffman table invariant. -/

namespace Zlib.Inftrees.TableABI
open C Zlib.Inftrees.Proofs

private abbrev Locals := InflateTableLocals
private abbrev Count := Array UInt16
private abbrev Return := Int32 × CodePtr × UInt32
private abbrev Step := LoopStep (Locals × Count) Return

/-- The old proof keeps immutable locals in the context and mutable ones in TS. -/
def locals (c : Ctx) (s : TS) : InflateTableLocals :=
  { len := s.len, sym := s.sym, min := s.min, max := c.max, root := c.root,
    curr := s.curr, drop := s.drop, left := s.left, used := s.used, huff := s.huff,
    incr := s.incr, fill := s.fill, low := s.low, mask := s.mask, here := s.here,
    next := s.next, base := c.base, extra := c.extra, match_ := c.match_ }

private def putSize (l : Locals) (curr : UInt32) (left : Int32) : Locals := {l with curr, left}
private def sizeGuard (l : Locals) : M (Bool × Locals) := pure (l.curr + l.drop < l.max, l)
private def sizeStep (count : Count) (s : Locals) : M (LoopStep Locals Empty) := do
  let cc ← cinline (geta count (s.curr + s.drop).toNat)
  let left ← cinline (chk32 (s.left.toInt - cc.toNat))
  let s := {s with left}
  if s.left ≤ 0 then return .brk s
  let s := {s with curr := s.curr + 1}
  let doubled ← cinline (chk32 (s.left.toInt * 2))
  return .next {s with left := doubled}

private theorem size_step_sim (l : Locals) (count : Count) (curr : UInt32) (left : Int32) :
    Sim (fun (n, balance, brk) => if brk then .brk (putSize l n balance) else .next (putSize l n balance))
      (sizeBody count l.drop (curr, left, false)) (sizeStep count (putSize l curr left)) := by
  intro h s H run
  simp only [sizeBody, sizeStep, putSize, cinline_eq, bind_app] at run ⊢
  cases g : geta count (curr + l.drop).toNat h with
  | error fault => rw [g] at run; cases run
  | ok p =>
    obtain ⟨cc, mid⟩ := p
    simp only [g] at run ⊢
    cases k : chk32 (left.toInt - cc.toNat) mid with
    | error fault => simp [k] at run
    | ok p =>
      obtain ⟨v, after⟩ := p
      by_cases endScan : v ≤ 0
      · simp only [k, endScan, ↓reduceIte, pure_app] at run ⊢; cases run; rfl
      · simp only [k, endScan, ↓reduceIte, bind_app, pure_app] at run ⊢
        cases d : chk32 (v.toInt * 2) after with
        | error fault => simp [d] at run
        | ok p => obtain ⟨w, final⟩ := p; simp only [d] at run; cases run; rfl

private theorem size_sim (l : Locals) (count : Count) :
    Sim (fun (curr,left,_) => putSize l curr left)
      (cwhile (sizeCond l.drop l.max) (sizeBody count l.drop) (l.curr, l.left, false))
      (cwhileBrk sizeGuard (sizeStep count) l) := by
  have loop (n : Nat) (curr : UInt32) (left : Int32) {h s H}
      (run : cwhile.go (sizeCond l.drop l.max) (sizeBody count l.drop) n (curr, left, false) h = .ok (s,H)) :
      cwhileCtrl.go sizeGuard (sizeStep count) n (putSize l curr left) h = .ok (.ok (putSize l s.1 s.2.1), H) := by
    induction n generalizing curr left h with
    | zero => cases run
    | succ n ih =>
      rw [cwhile.go, bind_app] at run
      rw [cwhileCtrl.go, bind_app]
      simp only [sizeCond, sizeGuard, putSize, Bool.not_false, Bool.true_and, pure_app] at run ⊢
      by_cases more : curr + l.drop < l.max <;>
        simp only [more, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] at run ⊢
      case neg => cases run; rfl
      rw [bind_app] at run ⊢
      cases step : sizeBody count l.drop (curr, left, false) h with
      | error fault => simp [step] at run
      | ok p =>
        obtain ⟨⟨ix, v, brk⟩, mid⟩ := p
        simp only [step] at run
        have got := size_step_sim l count curr left step
        cases brk <;> simp only [putSize, Bool.false_eq_true, ↓reduceIte] at got
        · rw [got]; exact ih ix v run
        · rw [got]
          cases n with
          | zero => cases run
          | succ n =>
            rw [cwhile.go, bind_app] at run
            simp only [sizeCond, Bool.not_true, Bool.false_and, pure_app, Bool.false_eq_true, ↓reduceIte] at run
            cases run; rfl
  intro h s H run
  unfold cwhileBrk cwhileCtrl
  have init : putSize l l.curr l.left = l := by cases l; rfl
  have finish := loop fuel l.curr l.left run
  rw [init] at finish
  rw [bind_ok finish]
  cases s with | mk _ p => cases p; rfl

def stepResult (c : Ctx) (bits : UInt32) (s : TS) :
    LoopStep (InflateTableLocals × Array UInt16) (Int32 × CodePtr × UInt32) :=
  if s.exit == 2 then .ret (1, c.table, bits)
  else if s.exit == 0 then .next (locals c s, s.count)
  else .brk (locals c s, s.count)

private def linkEntries (c : Ctx) (s : Locals) (count : Count) : M Step := do
  let s := {s with low := s.huff &&& s.mask}
  let q1 ← cinline (c.table.add s.low.toNat)
  let e1 ← cinline q1.load
  q1.store {e1 with op := s.curr.toUInt8}
  let q2 ← cinline (c.table.add s.low.toNat)
  let e2 ← cinline q2.load
  q2.store {e2 with bits := s.root.toUInt8}
  let d ← cinline (s.next.diff c.table)
  let q3 ← cinline (c.table.add s.low.toNat)
  let e3 ← cinline q3.load
  q3.store {e3 with val := d.toUInt64.toUInt16}
  return .next (s, count)

private def openSubtable (c : Ctx) (bits : UInt32) (s : Locals) (count : Count) : M Step := do
  let next ← cinline (s.next.add s.min.toNat)
  let s := {s with next, curr := s.len - s.drop}
  let left ← cinline (shl1i32 s.curr)
  let s := {s with left}
  let s ← cwhileBrk sizeGuard (sizeStep count) s
  let u ← cinline (shl32 1 s.curr)
  let s := {s with used := s.used + u}
  if tooBig c.type s.used then return .ret (1, c.table, bits)
  linkEntries c s count

/-- Follow the same checked memory operation in both executions. -/
theorem sameBind {α β γ : Type} {m : M α} {k : α → M β} {f : α → M γ}
    {h : Heap} {r : β} {v : γ} {H : Heap}
    (run : (m >>= k) h = .ok (r, H))
    (cont : ∀ x mid, k x mid = .ok (r, H) → f x mid = .ok (v, H)) :
    (m >>= f) h = .ok (v, H) := by
  rw [bind_app] at run ⊢
  cases e : m h with
  | error fault => simp [e] at run
  | ok p => obtain ⟨x, mid⟩ := p; simp only [e] at run; exact cont x mid run

/-- Keep the successful execution of the old loop when transporting its
continuation, so its frame theorem can be applied at the join. -/
private theorem relatedBind_run {α β γ δ : Type} {m : M α} {n : M β} {k : α → M γ} {f : β → M δ}
    {embed : α → β} {h : Heap} {r : γ} {v : δ} {H : Heap}
    (related : Sim embed m n) (run : (m >>= k) h = .ok (r,H))
    (cont : ∀ x mid, m h = .ok (x,mid) → k x mid = .ok (r,H) → f (embed x) mid = .ok (v,H)) :
    (n >>= f) h = .ok (v,H) := by
  rw [bind_app] at run
  cases step : m h with
  | error fault => simp [step] at run
  | ok p =>
    obtain ⟨x, mid⟩ := p
    rw [bind_ok (related step)]
    simp only [step] at run
    exact cont x mid step run

theorem relatedBind {α β γ δ : Type} {m : M α} {n : M β} {k : α → M γ} {f : β → M δ}
    {embed : α → β} {h : Heap} {r : γ} {v : δ} {H : Heap}
    (related : Sim embed m n) (run : (m >>= k) h = .ok (r, H))
    (cont : ∀ x mid, k x mid = .ok (r,H) → f (embed x) mid = .ok (v,H)) :
    (n >>= f) h = .ok (v,H) := by
  exact relatedBind_run related run (fun x mid _ tail => cont x mid tail)

private theorem open_sim (c : Ctx) (s : TS) (bits : UInt32) (active : s.exit = 0) :
    Sim (stepResult c bits) (openBody c s) (openSubtable c bits (locals c s) s.count) := by
  intro h r H run
  unfold openBody at run
  unfold openSubtable
  apply sameBind run
  intro ptr h run
  apply sameBind run
  intro balance h run
  let pending := {s with next := ptr, curr := s.len - s.drop, left := balance}
  apply relatedBind (size_sim (locals c pending) s.count) run
  rintro ⟨ix, left, _⟩ h run
  apply sameBind run
  intro u h run
  by_cases limit : tooBig c.type (s.used + u) = true
  · simp only [limit, ↓reduceIte, locals, putSize, pending, pure_app] at run ⊢
    cases run; rfl
  simp only [limit, Bool.false_eq_true, ↓reduceIte, locals, putSize, pending, linkEntries, cinline_eq] at run ⊢
  iterate 10 (apply sameBind run; intro val mid run)
  cases run
  simp only [stepResult, active]
  rfl

private def maybeOpen (c : Ctx) (bits : UInt32) (s : Locals) (count : Count) : M Step :=
  if s.len > s.root && (s.huff &&& s.mask) != s.low then
    if s.drop == 0 then openSubtable c bits {s with drop := s.root} count else openSubtable c bits s count
  else pure (.next (s,count))

private theorem maybeOpen_sim (c : Ctx) (s : TS) (bits : UInt32) (active : s.exit = 0) :
    Sim (stepResult c bits) (jp2 c s) (maybeOpen c bits (locals c s) s.count) := by
  intro h r H run
  unfold jp2 at run
  unfold maybeOpen
  by_cases sub : (decide (s.len > c.root) && (s.huff &&& s.mask) != s.low) = true
  · by_cases drop : (s.drop == 0) = true <;>
      simp only [locals, sub, drop, Bool.false_eq_true, ↓reduceIte] at run ⊢
    · erw [ite_eq_left sub]
      exact open_sim c {s with drop := c.root} bits active run
    · erw [ite_eq_left sub]
      exact open_sim c s bits active run
  · simp only [locals, sub, Bool.false_eq_true, ↓reduceIte, pure_app] at run ⊢
    erw [ite_eq_right sub]
    cases run; simp [stepResult, active, locals]

private def nextLength (c : Ctx) (bits : UInt32) (s : Locals) (count : Count) : M Step := do
  let s := {s with sym := s.sym + 1}
  let cl ← cinline (geta count s.len.toNat)
  let count ← seta count s.len.toNat (cl - 1)
  let clCheck ← cinline (geta count s.len.toNat)
  if clCheck == 0 then
    if s.len == s.max then return .brk (s,count)
    let w ← cinline (c.work.index s.sym.toNat)
    let lv ← cinline (c.lens.index w.toNat)
    maybeOpen c bits {s with len := lv.toUInt32} count
  else maybeOpen c bits s count

private theorem read_set {a b : Count} {i : Nat} {v : UInt16} {h mid : Heap}
    (set : seta a i v h = .ok (b, mid)) : geta b i mid = .ok (v, mid) := by
  by_cases inside : i < a.size
  · rw [seta_eq inside, pure_app] at set
    cases set
    unfold geta
    rw [getElem?_set!_self inside]
    rfl
  · simp [seta, inside, ub] at set

private theorem nextLength_sim (c : Ctx) (s : TS) (bits : UInt32) (active : s.exit = 0) :
    Sim (stepResult c bits) (jp1 c s) (nextLength c bits (locals c s) s.count) := by
  intro h r H run
  unfold jp1 at run
  unfold nextLength
  apply sameBind run
  intro cl h run
  rw [bind_app] at run
  cases set : seta s.count s.len.toNat (cl - 1) h with
  | error fault => rw [set] at run; cases run
  | ok p =>
    obtain ⟨count, mid⟩ := p
    simp only [set] at run
    have get := read_set set
    erw [bind_ok set, bind_ok get]
    let t := {s with sym := s.sym + 1, count := count}
    by_cases last : (cl - 1 == 0) = true <;>
      simp only [last, Bool.false_eq_true, ↓reduceIte] at run ⊢
    · by_cases done : (s.len == c.max) = true <;> simp only [locals, done, ↓reduceIte] at run ⊢
      · cases run; rfl
      erw [ite_eq_right done]
      apply sameBind run
      intro w h run
      apply sameBind run
      intro len h run
      exact maybeOpen_sim c {t with len := len.toUInt32} bits active run
    · exact maybeOpen_sim c t bits active run

private def fillOne (s : Locals) : M Locals := do
  let s := {s with fill := s.fill - s.incr}
  let hd ← cinline (shr32 s.huff s.drop)
  let q ← cinline (s.next.add (hd + s.fill).toNat)
  Ptr.store q s.here
  pure s

private theorem fill_sim (c : Ctx) (s : TS) :
    Sim (locals c) (cdoWhile fillBody fillCond s)
      (cdoWhile fillOne (fun l => pure (l.fill != 0, l)) (locals c s)) := by
  refine @doWhile_sim TS Locals (locals c) (fun t => t.fill != 0)
    fillBody fillOne fillCond (fun l => pure (l.fill != 0, l)) (fun _ _ => ⟨rfl, rfl⟩) ?_ s
  intro t h r H run
  unfold fillBody at run
  unfold fillOne
  apply sameBind run
  intro hd mid run
  unfold storeCode at run
  rw [bind_app] at run
  cases add : t.next.add ((hd + (t.fill - t.incr)).toNat : Int) mid with
  | error fault => simp only [bind_app, add, reduceCtorEq] at run
  | ok p =>
    obtain ⟨q, h'⟩ := p
    simp only [bind_app, add] at run
    erw [bind_ok add]
    cases wr : Ptr.store q t.here h' with
    | error fault => rw [wr] at run; cases run
    | ok p => obtain ⟨u, f⟩ := p; rw [wr] at run; erw [bind_ok wr]; cases run; rfl

private theorem incr_sim (c : Ctx) (s : TS) :
    Sim (locals c) (cwhile incrCond incrBody s)
      (cwhile (fun l => pure (l.huff &&& l.incr != 0, l))
        (fun l => pure {l with incr := l.incr >>> 1}) (locals c s)) := by
  refine @while_sim TS Locals (locals c) (fun t => t.huff &&& t.incr != 0) _ _ incrBody _
    (fun _ _ => ⟨rfl, rfl⟩) ?_ s
  intro t h r H run
  cases run; rfl

private def saved (s : TS) := (s.count, s.exit)

/-- The store changes the table on the heap. Among the local variables, it
only changes the fill counter. -/
private theorem fill_saved {s result : TS} {h H : Heap} (run : cdoWhile fillBody fillCond s h = .ok (result,H)) :
    saved result = saved s := by
  unfold cdoWhile at run
  generalize fuel = n at run
  induction n generalizing s h with
  | zero => cases run
  | succ n ih =>
    rw [cdoWhile.go, bind_app] at run
    cases step : fillBody s h with
    | error fault => simp [step] at run
    | ok pair =>
      obtain ⟨v, mid⟩ := pair
      simp only [step, fillCond, bind_app, pure_app] at run
      have fields : saved v = saved s := by
        unfold fillBody at step
        rw [bind_app] at step
        cases shift : shr32 s.huff s.drop h with
        | error fault => rw [shift] at step; cases step
        | ok pair =>
          obtain ⟨hd, h'⟩ := pair
          simp only [shift, bind_app, pure_app] at step
          cases store : storeCode s.next (hd + (s.fill - s.incr)).toNat s.here h' with
          | error fault => rw [store] at step; cases step
          | ok pair => obtain ⟨_, _⟩ := pair; rw [store] at step; cases step; rfl
      split at run
      · exact (ih run).trans fields
      · cases run; exact fields

private theorem incr_saved {s result : TS} {h H : Heap} (run : cwhile incrCond incrBody s h = .ok (result,H)) :
    saved result = saved s := by
  unfold cwhile at run
  generalize fuel = n at run
  induction n generalizing s with
  | zero => cases run
  | succ n ih =>
    rw [cwhile.go, bind_app] at run
    simp only [incrCond, pure_app] at run
    split at run
    · simp only [incrBody, bind_app, pure_app] at run
      exact ih (s := {s with incr := s.incr >>> 1}) run
    · cases run; rfl

private def writeEntries (c : Ctx) (bits : UInt32) (s : Locals) (count : Count) : M Step := do
  let incr ← cinline (shl32 1 (s.len - s.drop))
  let fill ← cinline (shl32 1 s.curr)
  let s := {s with incr, fill, min := fill}
  let s ← cdoWhile fillOne (fun l => pure (l.fill != 0, l)) s
  let incr ← cinline (shl32 1 (s.len - 1))
  let s := {s with incr}
  let s ← cwhile (fun l => pure (l.huff &&& l.incr != 0, l)) (fun l => pure {l with incr := l.incr >>> 1}) s
  if s.incr != 0 then nextLength c bits {s with huff := (s.huff &&& (s.incr - 1)) + s.incr} count
  else nextLength c bits {s with huff := 0} count

private theorem writeEntries_sim (c : Ctx) (s : TS) (bits : UInt32) (active : s.exit = 0) :
    Sim (stepResult c bits) (jp0 c s) (writeEntries c bits (locals c s) s.count) := by
  intro h r H run
  unfold jp0 at run
  unfold writeEntries
  apply sameBind run
  intro incr h run
  apply sameBind run
  intro fill h run
  let t := {s with incr, fill, min := fill}
  apply relatedBind_run (fill_sim c t) run
  intro u h full run
  have first := fill_saved full
  apply sameBind run
  intro incr h run
  apply relatedBind_run (incr_sim c {u with incr}) run
  intro v h advanced run
  have second := incr_saved advanced
  have same : saved v = saved s := second.trans first
  have count : v.count = s.count := congrArg Prod.fst same
  have act : v.exit = 0 := (congrArg Prod.snd same).trans active
  by_cases nonzero : (v.incr != 0) = true <;>
    simp only [locals, nonzero, ↓reduceIte, ← count] at run ⊢
  · exact nextLength_sim c {v with huff := (v.huff &&& (v.incr - 1)) + v.incr} bits act run
  · erw [ite_eq_right nonzero]
    exact nextLength_sim c {v with huff := 0} bits act run

/-- One iteration of the C-shaped table builder. The cases are cut at the
same joins as the original computation. -/
def tableStep (c : Ctx) (bits : UInt32) :
    InflateTableLocals × Array UInt16 → M (LoopStep (InflateTableLocals × Array UInt16) (Int32 × CodePtr × UInt32)) :=
  fun (s, count) => do
    let s := {s with here := {s.here with bits := (s.len - s.drop).toUInt8}}
    let w ← cinline (c.work.index s.sym.toNat)
    if w.toUInt32 + 1 < s.match_ then
      let val ← cinline (c.work.index s.sym.toNat)
      writeEntries c bits {s with here := {s.here with op := 0, val}} count
    else
      let w ← cinline (c.work.index s.sym.toNat)
      if w.toUInt32 ≥ s.match_ then
        let w ← cinline (c.work.index s.sym.toNat)
        let e ← cinline (geta s.extra (w.toUInt32 - s.match_).toNat)
        let w ← cinline (c.work.index s.sym.toNat)
        let val ← cinline (geta s.base (w.toUInt32 - s.match_).toNat)
        writeEntries c bits {s with here := {s.here with op := e.toUInt8, val}} count
      else writeEntries c bits {s with here := {s.here with op := 96, val := 0}} count

theorem step_sim (c : Ctx) (s : TS) (bits : UInt32) (active : s.exit = 0) :
    Sim (stepResult c bits) (buildStep c s) (tableStep c bits (locals c s, s.count)) := by
  intro h r H run
  rw [buildStep_eq] at run
  unfold hereTop at run
  unfold tableStep
  let t := {s with here := {s.here with bits := (s.len - s.drop).toUInt8}}
  apply sameBind run
  intro w h run
  by_cases lit : w.toUInt32 + 1 < c.match_ <;> simp only [locals, lit, ↓reduceIte] at run ⊢
  · apply sameBind run
    intro v h run
    exact writeEntries_sim c {t with here := {t.here with op := 0, val := v}} bits active run
  apply sameBind run
  intro w h run
  by_cases lookup : w.toUInt32 ≥ c.match_ <;> simp only [lookup, ↓reduceIte] at run ⊢
  · apply sameBind run
    intro w h run
    apply sameBind run
    intro e h run
    apply sameBind run
    intro w h run
    apply sameBind run
    intro v h run
    exact writeEntries_sim c {t with here := {t.here with op := e.toUInt8, val := v}} bits active run
  · exact writeEntries_sim c {t with here := {t.here with op := 96, val := 0}} bits active run

private def loopResult (c : Ctx) (bits : UInt32) (s : TS) : Except Return (Locals × Count) :=
  if s.exit == 2 then .error (1, c.table, bits) else .ok (locals c s, s.count)

private theorem table_loop_sim (c : Ctx) (bits : UInt32) (s : TS) (active : s.exit = 0) :
    Sim (loopResult c bits) (cwhile (fun t => pure (t.exit == 0,t)) (buildStep c) s)
      (cforEver (tableStep c bits) (locals c s,s.count)) := by
  intro h r H run
  unfold cforEver
  unfold cwhile at run
  generalize fuel = n at run ⊢
  induction n generalizing s h with
  | zero => cases run
  | succ n ih =>
    rw [cwhile.go, bind_app] at run
    simp only [active, BEq.rfl, pure_app, ↓reduceIte, bind_app] at run
    cases e : buildStep c s h with
    | error fault => simp [e] at run
    | ok p =>
      obtain ⟨t, mid⟩ := p
      simp only [e] at run
      rw [cforEver.go, bind_ok (step_sim c s bits active e)]
      by_cases again : t.exit = 0
      · simp only [stepResult, again, BEq.rfl, ↓reduceIte]
        exact ih t again run
      have stop : (t.exit == 0) = false := beq_eq_false_iff_ne.mpr again
      cases n with
      | zero => cases run
      | succ n =>
        rw [cwhile.go, bind_app] at run
        simp only [pure_app, stop, Bool.false_eq_true, ↓reduceIte] at run
        cases run
        cases endCode : r.exit == 2 <;> simp only [stepResult, loopResult, endCode, stop,
          Bool.false_eq_true, ↓reduceIte, pure_app]

/-- The operations after the final break in the C-shaped builder. -/
def finishTable (table : CodePtr) : InflateTableLocals × Array UInt16 → M (Int32 × CodePtr × UInt32) :=
  fun (s, _) => do
    let mut s := s
    if s.huff != 0 then
      s := {s with here := ⟨64, (s.len - s.drop).toUInt8, 0⟩}
      let q ← cinline (s.next.add s.huff.toNat)
      Ptr.store q s.here
    let table ← cinline (table.add s.used.toNat)
    return (0, table, s.root)

def finishOld (c : Ctx) (bits : UInt32) (s : TS) : M Return := do
  if s.exit == 2 then return (1, c.table, bits)
  let mut s := s
  if s.huff != 0 then
    s := {s with here := ⟨64, (s.len - s.drop).toUInt8, 0⟩}
    storeCode s.next s.huff.toNat s.here
  let table ← c.table.add s.used.toNat
  return (0, table, c.root)

private theorem finish_eq (c : Ctx) (bits : UInt32) (s : TS) (h : Heap) :
    (match loopResult c bits s with
     | .error x => pure x
     | .ok pair => finishTable c.table pair) h = finishOld c bits s h := by
  unfold loopResult finishOld
  cases s.exit == 2 <;> simp only [Bool.false_eq_true, ↓reduceIte]
  unfold finishTable
  cases tail : s.huff != 0 <;> simp only [locals, tail, Bool.false_eq_true, ↓reduceIte, cinline_eq, storeCode, bind_assoc_table]

/-- A successful execution of the old outer loop has the same result, root,
table pointer and heap as the explicit C break/return loop. -/
theorem build_loop_sim (c : Ctx) (bits : UInt32) (s : TS) (active : s.exit = 0) :
    Sim id (cwhile (fun t => pure (t.exit == 0,t)) (buildStep c) s >>= finishOld c bits)
      (cforEverRet (tableStep c bits) (locals c s,s.count) (finishTable c.table)) := by
  intro h r H run
  unfold cforEverRet
  apply relatedBind (table_loop_sim c bits s active) run
  intro t mid tail
  have out := (finish_eq c bits t mid).trans tail
  cases final : loopResult c bits t <;> simp only [final, id_eq] at out ⊢ <;> exact out

#print axioms build_loop_sim
end Zlib.Inftrees.TableABI
