import ZlibF.Proof.«inflate.c.leave-restore»
import ZlibF.Spec.Functional.Checksums

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual counters, checksum, data-type and return suffix. The stream
value is the one read before updatewindow in inf_leave. -/
def leaveFinalize (c : Ctx) (l : IL) (z : ZStream) : M Int32 := do
  -- in -= strm->avail_in; out -= strm->avail_out;
  let in_ := l.in_ - z.avail_in
  let out_ := l.out_ - z.avail_out
  -- strm->total_in += in; strm->total_out += out; state->total += out;
  wrZ c.strm fun z => { z with total_in := z.total_in + in_.toUInt64, total_out := z.total_out + out_.toUInt64 }
  wrS c.st fun s => { s with total := s.total + out_.toUInt64 }
  -- if ((state->wrap & 4) && out) strm->adler = state->check = UPDATE_CHECK(state->check, strm->next_out - out, out);
  let s ← ldInflateState c.st
  if (s.wrap &&& 4) != 0 && out_ != 0 then
    let p ← z.next_out.add (-(out_.toNat : Int))
    let v ← UPDATE_CHECK c.st s.check p out_
    wrS c.st fun s => { s with check := v }
    wrZ c.strm fun z => { z with adler := v }
  -- strm->data_type = (int)state->bits + (state->last ? 64 : 0) + (state->mode == TYPE ? 128 : 0) +
  --                   (state->mode == LEN_ || state->mode == COPY_ ? 256 : 0);
  let s ← ldInflateState c.st
  let dt ← chkI32 ((u2i s.bits).toInt + (if s.last != 0 then 64 else 0) + (if s.mode == TYPE then 128 else 0) +
    (if s.mode == LEN_ || s.mode == COPY_ then 256 else 0))
  wrZ c.strm fun z => { z with data_type := dt }
  -- if (((in == 0 && out == 0) || flush == Z_FINISH) && ret == Z_OK) ret = Z_BUF_ERROR;
  let mut ret := l.ret
  if ((in_ == 0 && out_ == 0) || c.flush == Z_FINISH) && ret == Z_OK then ret := Z_BUF_ERROR
  return ret

/-- The final data_type assignment and return selection. -/
def leaveReturn (c : Ctx) (l : IL) (z : ZStream) : M Int32 := do
  let in_ := l.in_ - z.avail_in
  let out_ := l.out_ - z.avail_out
  -- strm->data_type = (int)state->bits + (state->last ? 64 : 0) + (state->mode == TYPE ? 128 : 0) +
  --                   (state->mode == LEN_ || state->mode == COPY_ ? 256 : 0);
  let s ← ldInflateState c.st
  let dt ← chkI32 ((u2i s.bits).toInt + (if s.last != 0 then 64 else 0) + (if s.mode == TYPE then 128 else 0) +
    (if s.mode == LEN_ || s.mode == COPY_ then 256 else 0))
  wrZ c.strm fun z => { z with data_type := dt }
  -- if (((in == 0 && out == 0) || flush == Z_FINISH) && ret == Z_OK) ret = Z_BUF_ERROR;
  let mut ret := l.ret
  if ((in_ == 0 && out_ == 0) || c.flush == Z_FINISH) && ret == Z_OK then ret := Z_BUF_ERROR
  return ret

/-- The two actual counter writes. -/
def leaveCounters (c : Ctx) (l : IL) (z : ZStream) : M Unit := do
  -- in -= strm->avail_in; out -= strm->avail_out;
  let in_ := l.in_ - z.avail_in
  let out_ := l.out_ - z.avail_out
  -- strm->total_in += in; strm->total_out += out; state->total += out;
  wrZ c.strm fun z => { z with total_in := z.total_in + in_.toUInt64, total_out := z.total_out + out_.toUInt64 }
  wrS c.st fun s => { s with total := s.total + out_.toUInt64 }

/-- The actual optional output checksum update. -/
def leaveChecksum (c : Ctx) (l : IL) (z : ZStream) : M Unit := do
  let out_ := l.out_ - z.avail_out
  -- if ((state->wrap & 4) && out) strm->adler = state->check = UPDATE_CHECK(state->check, strm->next_out - out, out);
  let s ← ldInflateState c.st
  if (s.wrap &&& 4) != 0 && out_ != 0 then
    let p ← z.next_out.add (-(out_.toNat : Int))
    let v ← UPDATE_CHECK c.st s.check p out_
    wrS c.st fun s => { s with check := v }
    wrZ c.strm fun z => { z with adler := v }

private theorem leave_bind_assoc {α β γ : Type} (m : M α) (f : α → M β) (g : β → M γ) :
    (m >>= f >>= g) = (m >>= fun x => f x >>= g) := by
  funext h
  simp only [bind_app]
  cases m h <;> rfl

private theorem leave_ite_bind {α β : Type} (b : Bool) (yes no : M α) (f : α → M β) :
    ((if b then yes else no) >>= f) = (if b then yes >>= f else no >>= f) := by
  cases b <;> rfl

private theorem leave_pure_bind {α β : Type} (a : α) (f : α → M β) :
    (pure a >>= f) = f a := rfl

/-- Literal source decomposition; each stage below is proved by execution. -/
theorem leaveFinalize_split (c : Ctx) (l : IL) (z : ZStream) :
    leaveFinalize c l z = (do leaveCounters c l z; leaveChecksum c l z; leaveReturn c l z) := by
  unfold leaveFinalize leaveCounters leaveChecksum leaveReturn
  simp only [leave_bind_assoc, leave_ite_bind, leave_pure_bind]

/-- The source reaches this suffix directly when no window update is due. -/
theorem leaveAfterRestore_no_window {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (skip : (s.wsize != 0 || (l.out_ != z.avail_out && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = false) :
    leaveAfterRestore c l h = leaveFinalize c l z h := by
  unfold leaveAfterRestore leaveFinalize
  rw [E.strm, E.st]
  simp only [bind_app, ldZ_eq, E.hz, ldI_eq, E.hs, skip, Bool.false_eq_true, ↓reduceIte]

/-- The cast used in data_type stays signed and bounded. -/
theorem leave_data_type_safe (s : InflateState) (bits : s.bits.toNat ≤ 39) :
    ∃ dt, chkI32 ((u2i s.bits).toInt + (if s.last != 0 then 64 else 0) +
      (if s.mode == TYPE then 128 else 0) +
      (if s.mode == LEN_ || s.mode == COPY_ then 256 else 0)) = pure dt := by
  have cast : (u2i s.bits).toInt = (s.bits.toNat : Int) := by
    unfold u2i
    rw [Int32.toInt_ofInt_of_le (by omega) (by omega)]
  refine ⟨Int32.ofInt _, chkI32_ok ?_ ?_⟩
  all_goals rw [cast]; split <;> split <;> split <;> omega

/-- The final metadata and return operations execute without a signed cast
fault. Only data_type is written; the private state is unchanged. -/
theorem leaveReturn_run {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z current : ZStream} {s : InflateState} (E : Env c h r zs current s)
    (bits : s.bits.toNat ≤ 39) :
    ∃ dt, chkI32 ((u2i s.bits).toInt + (if s.last != 0 then 64 else 0) +
      (if s.mode == TYPE then 128 else 0) +
      (if s.mode == LEN_ || s.mode == COPY_ then 256 else 0)) = pure dt ∧
      leaveReturn c l z h = .ok
      ((if ((l.in_ - z.avail_in == 0 && l.out_ - z.avail_out == 0 || c.flush == Z_FINISH) &&
        l.ret == Z_OK) then Z_BUF_ERROR else l.ret), r.put h { current with data_type := dt }) := by
  obtain ⟨dt, cast⟩ := leave_data_type_safe s bits
  refine ⟨dt, cast, ?_⟩
  unfold leaveReturn
  rw [E.st, E.strm]
  simp only [bind_app, ldI_eq, E.hs, cast, pure_app, wrZ_eq, E.hz]
  split <;> rfl

/-- The exact stream counter update. -/
def leaveCountStream (current z : ZStream) (l : IL) : ZStream :=
  { current with total_in := current.total_in + (l.in_ - z.avail_in).toUInt64, total_out := current.total_out + (l.out_ - z.avail_out).toUInt64 }

/-- The exact private output counter update. -/
def leaveCountState (s : InflateState) (z : ZStream) (l : IL) : InflateState :=
  { s with total := s.total + (l.out_ - z.avail_out).toUInt64 }

theorem leaveCounters_run {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z current : ZStream} {s : InflateState} (E : Env c h r zs current s) :
    leaveCounters c l z h = .ok ((),
      setI (r.put h (leaveCountStream current z l)) zs (leaveCountState s z l)) := by
  unfold leaveCounters
  rw [E.strm, E.st]
  simp only [bind_app, wrZ_eq, E.hz, ZStreamRef.put_istates, wrI_eq, E.hs]
  rfl

/-- No counter or checksum write changes a decoder field. -/
def LeaveMetadataFrame (before after : InflateState) : Prop :=
  after = { before with total := after.total, check := after.check }

theorem LeaveMetadataFrame.trans {first second third : InflateState}
    (a : LeaveMetadataFrame first second) (b : LeaveMetadataFrame second third) :
    LeaveMetadataFrame first third := by
  unfold LeaveMetadataFrame at *
  rw [b, a]

/-- Metadata writes preserve every actual decoder-table view. -/
theorem leave_metadata_code_views {h : Heap} {r : ZStreamRef} {zs : Nat} {s state : InflateState}
    (get : h.istates zs = some s) (stream : ZStream) (frame : LeaveMetadataFrame s state) (ref : CodeRef) :
    (Space.get (setI (r.put h stream) zs state) ref : Option (Array Code)) = Space.get h ref := by
  cases ref with
  | istate_codes i =>
    by_cases same : i = zs
    · subst i
      simp only [Space.get, setI_istates_same, get, Option.map_some]
      rw [frame]
    · simp only [Space.get, setI_istates_ne _ _ _ _ same, ZStreamRef.put_istates]
  | st_lenfix => simp only [Space.get, setI, ZStreamRef.put_static]
  | st_distfix => simp only [Space.get, setI, ZStreamRef.put_static]

/-- The guarded scalar clause is unaffected by counter/checksum metadata. -/
theorem LeaveMetadataFrame.pending {s state : InflateState} (frame : LeaveMetadataFrame s state)
    (pending : DataPendingInvariant s) : DataPendingInvariant state := by
  rw [frame]
  exact ⟨pending.sane, pending.lenext, pending.dist, pending.distext, pending.matching⟩

/-- Table pointers, table sizes and table contents all survive metadata writes. -/
theorem LeaveMetadataFrame.tables {h after : Heap} {s state : InflateState}
    (frame : LeaveMetadataFrame s state)
    (views : ∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref)
    (tables : DataTableInvariant h s) : DataTableInvariant after state := by
  intro active
  have oldActive : DataTableMode s.mode := by rw [frame] at active; exact active
  have safe := tables oldActive
  constructor
  · obtain ⟨ref, off, array, ptr, get, safe⟩ := safe.lengthTable
    exact ⟨ref, off, array, by rw [frame]; exact ptr, by rw [views]; exact get,
      by rw [frame]; exact safe⟩
  · obtain ⟨ref, off, array, ptr, get, safe⟩ := safe.distanceTable
    exact ⟨ref, off, array, by rw [frame]; exact ptr, by rw [views]; exact get,
      by rw [frame]; exact safe⟩
  · exact safe.lengthLeaves_frame (by rw [frame]) (by rw [frame]) (fun ref _ _ => views ref)

/-- Only a readable produced prefix is needed after the last output write. -/
def LeaveOutputView (h : Heap) (l : IL) : Prop :=
  ∃ ref off array, l.put = .ref ref off ∧ Space.get h ref = some array ∧
    (l.out_ - l.left).toNat ≤ off ∧ off ≤ array.size

theorem leaveOutputView_of_cursor {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {l : IL} (good : Good h r zs z s) (output : OutputCursorInvariant h r l) :
    LeaveOutputView h l := by
  obtain ⟨ref, array, off, ptr, get, _, room, count, made, _⟩ :=
    callerRange_slow_output good l output.range output.nonnull output.count output.produced
  refine ⟨ref, off, array, ptr, get, ?_, by omega⟩
  rw [UInt32.toNat_sub_of_le _ _ count]
  exact made

end Zlib.Inflate.Proofs
