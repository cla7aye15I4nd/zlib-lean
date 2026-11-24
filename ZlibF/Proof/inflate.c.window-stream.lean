import ZlibF.Proof.«inflate.c.byte-views»

namespace Zlib.Inflate.Proofs.WindowStream
open C Zlib.Inflate
set_option autoImplicit false

private def Preserves {α : Type} (r : ZStreamRef) (op : M α) : Prop :=
  ∀ h v after, op h = .ok (v, after) → r.get after = r.get h

private theorem bind {α β : Type} {r : ZStreamRef} {f : M α} {g : α → M β}
    (hf : Preserves r f) (hg : ∀ x, Preserves r (g x)) : Preserves r (f >>= g) := by
  intro h v after run
  rw [bind_app] at run
  cases one : f h with
  | error e => rw [one] at run; cases run
  | ok pair =>
    obtain ⟨x, mid⟩ := pair
    rw [one] at run
    exact (hg x mid v after run).trans (hf h x mid one)

private theorem pure' {α : Type} (r : ZStreamRef) (v : α) : Preserves r (pure v) := by
  intro h x after run; cases run; rfl

private theorem ldZ (r : ZStreamRef) (p : ZStreamPtr) : Preserves r (ldZStream p) := by
  intro h v after run
  cases p with
  | none => cases run
  | some p => rw [ldZ_eq] at run; split at run <;> cases run; rfl

private theorem ldS (r : ZStreamRef) (p : InflateStatePtr) : Preserves r (ldInflateState p) := by
  intro h v after run
  cases p with
  | none => cases run
  | some p => cases p with | tab i => rw [ldI_eq] at run; split at run <;> cases run; rfl

private theorem castI (r : ZStreamRef) (p : Option StateRef) : Preserves r (castInflateState p) := by
  intro h v after run
  cases p with
  | none => cases run; rfl
  | some p => cases p <;> cases run <;> rfl

private theorem stS (r : ZStreamRef) (p : InflateStatePtr) (v : InflateState) :
    Preserves r (stInflateState p v) := by
  intro h x after run
  cases p with
  | none => cases run
  | some p =>
    cases p with
    | tab i =>
      cases state : h.istates i with
      | none => simp [stInflateState, InflateStateRef.get, state] at run
      | some before => rw [stInflateState_tab state] at run; cases run; cases r <;> rfl

private theorem shift (r : ZStreamRef) (v n : UInt32) : Preserves r (shl32 v n) := by
  unfold shl32; split
  · exact pure' _ _
  · intro h x after run; cases run

private theorem add (r : ZStreamRef) (p : BPtr) (off : Int) : Preserves r (p.add off) := by
  intro h v after run
  unfold Ptr.add at run
  repeat' first | split at run | (cases run <;> rfl)

private theorem copy (r : ZStreamRef) (dst src : BPtr) (n : Nat) : Preserves r (memcpyB dst src n) := by
  intro h value after run
  cases dst with
  | null => cases run
  | ref dest off =>
    cases src with
    | null => cases run
    | ref src srcOff =>
      cases destGet : (Space.get h dest : Option (Array UInt8)) <;>
        cases srcGet : (Space.get h src : Option (Array UInt8))
      all_goals simp only [memcpyB, Ptr.memcpy, destGet, srcGet] at run
      all_goals first | cases run | skip
      rename_i array sourceArray
      rw [Space.modify_eq h dest array _ destGet] at run
      repeat' first | split at run | (cases run <;> exact byte_view_put_stream _ _ _ _)

private theorem alloc (r : ZStreamRef) (p : ZStreamPtr) (items size : UInt32) :
    Preserves r (ZALLOCB p items size) := by
  unfold ZALLOCB
  apply bind (ldZ _ _)
  intro z
  split
  · intro h x after run
    unfold Zlib.Zutil.zcalloc allocB at run
    repeat' first | split at run | (cases run <;> cases r <;> rfl)
  · intro h x after run; cases run

/-- Every returning window update preserves the entire observed stream, for both stream
representations. Includes the allocation-failure return. -/
theorem updatewindow_get (r : ZStreamRef) (p : ZStreamPtr) (end_ : BPtr) (n : UInt32)
    {h after : Heap} {rc : Int32} (run : updatewindow p end_ n h = .ok (rc, after)) :
    r.get after = r.get h := by
  have all : Preserves r (updatewindow p end_ n) := by
    unfold updatewindow
    repeat' first
      | exact ldZ _ _ | exact ldS _ _ | exact castI _ _ | exact stS _ _ _
      | exact alloc _ _ _ _ | exact shift _ _ _ | exact add _ _ _ | exact copy _ _ _ _
      | exact pure' _ _
      | refine bind ?_ (fun x => ?_)
      | split
      | dsimp only
  exact all h rc after run

private theorem ldS_same (p : InflateStatePtr) {h after : Heap} {v : InflateState}
    (run : ldInflateState p h = .ok (v, after)) : after = h := by
  cases p with
  | none => cases run
  | some p => cases p with | tab i => rw [ldI_eq] at run; split at run <;> cases run; rfl

private theorem sameBind {α β : Type} (op : M α) (f g : α → M β)
    (same : ∀ x, f x = g x) : (op >>= f) = (op >>= g) := by
  rw [funext same]

/-- Any continuation sees the stream captured at the window check on the current heap. -/
private theorem leaveWindow_congr (c : Ctx) (l : IL) (f g : ZStream → M Int32)
    (agree : ∀ (z : ZStream) (h : Heap), ldZStream c.strm h = .ok (z,h) → f z h = g z h) :
    leaveWindow c l f = leaveWindow c l g := by
  unfold leaveWindow
  apply sameBind; intro _
  apply sameBind; intro _
  funext h
  cases stream : c.strm with
  | none => simp only [bind_app]; rfl
  | some r =>
    cases present : r.get h with
    | none => simp only [bind_app, ldZ_eq, present]
    | some z =>
      have read := ldZStream_ok present
      simp only [bind_app, read]
      cases st : ldInflateState c.st h with
      | error e => rfl
      | ok result =>
        obtain ⟨v, h'⟩ := result
        have unchanged : h' = h := ldS_same c.st st
        subst h'
        dsimp only
        split
        · simp only [bind_app]
          cases updated : updatewindow (some r) z.next_out (l.out_ - z.avail_out) h with
          | error e => rfl
          | ok pair =>
            obtain ⟨rc, after⟩ := pair
            have current : r.get after = some z := (updatewindow_get r _ _ _ updated).trans present
            dsimp only
            by_cases failed : (rc != 0) = true
            · simp [failed]
            · simp only [failed, Bool.false_eq_true, ite_false]
              exact agree z after (by rw [stream]; exact ldZStream_ok current)
        · exact agree z h (by rw [stream]; exact read)

private theorem writeS (r : ZStreamRef) (p : InflateStatePtr) (f : InflateState → InflateState) :
    Preserves r (wrS p f) := bind (ldS r p) (fun v => stS r p (f v))

/-- Accounting changes the totals before the checksum is computed. The stream's output pointer
is still the same when the C checksum branch reads it. -/
private theorem accounting_output (c : Ctx) (l : IL) (z : ZStream) (h : Heap)
    (read : ldZStream c.strm h = .ok (z,h)) :
    leaveAccounting c l z (rdZ c.strm (·.next_out)) h =
    leaveAccounting c l z (pure z.next_out) h := by
  cases stream : c.strm with
  | none => rw [stream] at read; cases read
  | some r =>
    have present : r.get h = some z := by
      rw [stream, ldZ_eq] at read
      split at read <;> cases read
      assumption
    let counted := {z with
      total_in := z.total_in + (l.in_ - z.avail_in).toUInt64
      total_out := z.total_out + (l.out_ - z.avail_out).toUInt64}
    let h1 := r.put h counted
    have live : r.get h1 = some counted := ZStreamRef.get_put_same present _
    unfold leaveAccounting
    simp only [stream, bind_app, wrZ_eq, present]
    generalize stateRun : wrS c.st (fun s => {s with total := s.total + (l.out_ - z.avail_out).toUInt64}) h1 = result
    cases result with
    | error e => rfl
    | ok pair =>
      obtain ⟨u, h2⟩ := pair
      have current : r.get h2 = some counted := (writeS r _ _ h1 u h2 stateRun).trans live
      dsimp only
      cases loaded : ldInflateState c.st h2 with
      | error e => rfl
      | ok pair =>
        obtain ⟨v, h3⟩ := pair
        have eqHeap := ldS_same c.st loaded
        subst h3
        have pointer : rdZ (some r) (·.next_out) h2 = .ok (z.next_out,h2) := by
          simp only [rdZ, bind_app, ldZStream_ok current]; rfl
        dsimp only
        split <;> simp only [cinline, bind_app, pointer, pure_app]

/-- On the capture-based path, reading the saved output pointer is a pure operation. -/
theorem savedOutput_bind {α : Type} (p : BPtr) (f : BPtr → M α) :
    (cinline (pure p) >>= f) = f p := rfl

/-- The capture-based exit and the live reads in the original exit produce exactly the same
result or fault, including the complete returned heap. -/
theorem inflate_leave_eq_saved (c : Ctx) (l : IL) :
    inflate_leave c l = leaveWindow c l (fun z => leaveAccounting c l z (pure z.next_out)) := by
  unfold inflate_leave
  apply leaveWindow_congr
  intro z h read
  simp only [bind_app, read]
  exact accounting_output c l z h read

#print axioms inflate_leave_eq_saved
#print axioms updatewindow_get
end Zlib.Inflate.Proofs.WindowStream
