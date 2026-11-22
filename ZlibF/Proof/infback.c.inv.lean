import ZlibF.Proof.«infback.c.room»
import ZlibF.Proof.«inftrees.c.fixed»

/-!
# infback.c: the invariant at the top of the loop, and `case TYPE`

`LInv` is what holds whenever `for (;;) switch (state->mode)` is about to read the mode: the stream and the state record
exist, the window is the caller's writable block, `put`/`left` describe the unwritten tail of the window, the registers
describe the current input chunk (`BIn`), the call-backs' invariant holds, and at most 39 bits are held.
-/

namespace Zlib.Infback.Spec
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs

/-- The invariant of the dispatch loop. `c.strm = r`, `c.st = zs`; `z`, `s` are the stream and state records; `bs` the rest of
the current input chunk. -/
structure LInv (c : BCtx) (win : Nat) (ownI : Nat → Prop) (R : Heap → Prop) (r : ZStreamRef) (zs : Nat) (h : Heap)
    (l : IL) (z : ZStream) (s : InflateState) (bs : List UInt8) : Prop where
  cstrm : c.strm = some r
  cst : c.st = some (.tab zs)
  hz : r.get h = some z
  hs : h.istates zs = some s
  wf : s.WellFormed
  wnd : ∃ off a, s.window = .ref (.blk win) off ∧ h.bytes win = some a ∧ h.ro win = false ∧ off + s.wsize.toNat ≤ a.size
  put : ∃ off, s.window = .ref (.blk win) off ∧ l.put = .ref (.blk win) (off + (s.wsize.toNat - l.left.toNat)) ∧
    l.left.toNat ≤ s.wsize.toNat
  bin : BIn ownI h l bs
  hR : R h
  bits : l.bits.toNat ≤ 39

end Zlib.Infback.Spec

namespace Zlib.Infback.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Spec

theorem rdS_ok {c : BCtx} {zs : Nat} {h : Heap} {s : InflateState} (hc : c.st = some (.tab zs))
    (hs : h.istates zs = some s) {α : Type} (f : InflateState → α) : rdS c.st f h = .ok (f s, h) := by
  rw [hc, rdI_eq]; simp [hs]

theorem setMode_ok {c : BCtx} {zs : Nat} {h : Heap} {s : InflateState} (hc : c.st = some (.tab zs))
    (hs : h.istates zs = some s) (m : UInt32) : setMode c.st m h = .ok ((), setI h zs { s with mode := m }) := by
  rw [hc]; exact setMode_tab hs m

theorem wrS_ok {c : BCtx} {zs : Nat} {h : Heap} {s : InflateState} (hc : c.st = some (.tab zs))
    (hs : h.istates zs = some s) (f : InflateState → InflateState) : wrS c.st f h = .ok ((), setI h zs (f s)) := by
  rw [hc]; exact wrS_tab hs f

theorem wf_with {s : InflateState} (hw : s.WellFormed) (s' : InflateState) (e1 : s'.lens = s.lens) (e2 : s'.work = s.work)
    (e3 : s'.codes = s.codes) : s'.WellFormed := by
  unfold InflateState.WellFormed at *; rw [e1, e2, e3]; exact hw

/-- A write to the state record that keeps the window and the array sizes keeps the invariant. -/
theorem LInv.setS {c : BCtx} {win : Nat} {ownI : Nat → Prop} {R : Heap → Prop} {r : ZStreamRef} {zs : Nat} {h : Heap}
    {l : IL} {z : ZStream} {s : InflateState} {bs : List UInt8} (I : LInv c win ownI R r zs h l z s bs)
    (s' : InflateState) (hw : s'.window = s.window) (hsz : s'.wsize = s.wsize) (e1 : s'.lens = s.lens)
    (e2 : s'.work = s.work) (e3 : s'.codes = s.codes) (hR' : R (setI h zs s')) :
    LInv c win ownI R r zs (setI h zs s') l z s' bs := by
  obtain ⟨hcs, hct, hz, hs, wf, ⟨o1, a, w1, ba, ro, le⟩, ⟨o2, w2, pp, pl⟩, B, hR, hb⟩ := I
  refine ⟨hcs, hct, by simpa using hz, by simp, wf_with wf s' e1 e2 e3, ⟨o1, a, by rw [hw]; exact w1, by simpa using ba,
    by simpa using ro, by rw [hsz]; exact le⟩, ⟨o2, by rw [hw]; exact w2, by rw [hsz]; exact pp, by rw [hsz]; exact pl⟩,
    @BIn.congr ownI h (setI h zs s') l bs (fun _ _ => rfl) B, hR', hb⟩

/-- New registers (same `put` and `left`, a valid chunk, at most 39 bits) keep the invariant. -/
theorem LInv.regs {c : BCtx} {win : Nat} {ownI : Nat → Prop} {R : Heap → Prop} {r : ZStreamRef} {zs : Nat} {h : Heap}
    {l : IL} {z : ZStream} {s : InflateState} {bs : List UInt8} (I : LInv c win ownI R r zs h l z s bs) {l' : IL}
    {bs' : List UInt8} (hp : l'.put = l.put) (hl : l'.left = l.left) (B' : BIn ownI h l' bs')
    (hb : l'.bits.toNat ≤ 39) : LInv c win ownI R r zs h l' z s bs' := by
  obtain ⟨hcs, hct, hz, hs, wf, wnd, ⟨o2, w2, pp, pl⟩, B, hR, hb0⟩ := I
  exact ⟨hcs, hct, hz, hs, wf, wnd, ⟨o2, w2, by rw [hp, hl]; exact pp, by rw [hl]; exact pl⟩, B', hR, hb⟩

set_option maxRecDepth 100000 in
theorem msg_block_type : "invalid block type" ∈ strTable := by
  rw [Array.mem_def]; decide +kernel

theorem LInv.putMsg {c : BCtx} {win : Nat} {ownI : Nat → Prop} {R : Heap → Prop} {r : ZStreamRef} {zs : Nat} {h : Heap}
    {l : IL} {z : ZStream} {s : InflateState} {bs : List UInt8} (I : LInv c win ownI R r zs h l z s bs) (m : BPtr)
    (hR' : R (r.put h { z with msg := m })) :
    LInv c win ownI R r zs (r.put h { z with msg := m }) l { z with msg := m } s bs := by
  obtain ⟨hcs, hct, hz, hs, wf, ⟨o1, a, w1, ba, ro, le⟩, pt, B, hR, hb⟩ := I
  refine ⟨hcs, hct, by simp [hz], by simpa using hs, wf, ⟨o1, a, w1, by simpa using ba, by simpa using ro, le⟩, pt,
    @BIn.congr ownI h (r.put h { z with msg := m }) l bs (fun _ _ => by simp) B, hR', hb⟩

/-- `strm->msg = "..."; state->mode = BAD;` for a message that is a string literal. -/
theorem badMode_run (c : BCtx) {r : ZStreamRef} {zs : Nat} {h : Heap} {z : ZStream} {s : InflateState}
    (hcs : c.strm = some r) (hct : c.st = some (.tab zs)) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (msg : String) (hm : msg ∈ strTable) :
    ∃ i, badMode c msg h = .ok ((), setI (r.put h { z with msg := .ref (.str i) 0 }) zs { s with mode := BAD }) := by
  obtain ⟨i, hi, -⟩ := strLitRef_of_mem (h := h) hm
  refine ⟨i, ?_⟩
  have hs' : (r.put h { z with msg := .ref (.str i) 0 }).istates zs = some s := by simpa using hs
  have hz' : r.get (r.put h { z with msg := .ref (.str i) 0 }) = some { z with msg := .ref (.str i) 0 } := by simp [hz]
  unfold badMode setMsg Zlib.Zutil.strLit
  simp [bind_app, hi, hcs, ldZ_eq, hz, stZ_eq, setMode_ok hct hs']

end Zlib.Infback.Proofs
