import ZlibF.Spec.Safety.MultiStream
import ZlibF.Proof.«public-inflate-sequence-safety»
import ZlibF.Proof.«public-deflate-goals»
import ZlibF.Proof.«public-deflate-copy»
import ZlibF.Proof.«public-init-safety»
import ZlibF.Proof.«public-deflate-init-domain»
import ZlibF.Proof.«public-inflate-init»
import ZlibF.Proof.«inflate.c.completes-keep-run»
import ZlibF.Proof.«inflate.c.default-entry»
import ZlibF.Proof.«public-inflate-end»
import ZlibF.Proof.«public-deflate-end»

/-!
# Multi-stream compositionality and non-interference safety proofs

Proves `Goal.multi_stream_init_disjoint`, `Goal.multi_stream_step_safety`,
`Goal.multi_stream_end_safety`, and `Goal.multi_stream_nonvacuity` by combining
the single-stream sequence safety contracts (`inflate_sequence_safety_public`,
`deflate_sequence_safety`), `HeapUniq` disjointness, `restoreRegions` preservation,
and non-stealing ownership lemmas for every permitted stream operation.
-/

namespace ZlibF.Spec.Public.MultiStreamProof
open C ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false
set_option maxHeartbeats 2000000

private theorem uniq_ne_none {h : Heap} (hu : Zlib.Inflate.Spec.Uniq h) {b : Nat} :
    (h.bytes b ≠ none → h.words b = none ∧ h.streams b = none ∧ h.gzheaders b = none ∧
        h.dstates b = none ∧ h.istates b = none ∧ h.gzstates b = none) ∧
    (h.words b ≠ none → h.bytes b = none ∧ h.streams b = none ∧ h.gzheaders b = none ∧
        h.dstates b = none ∧ h.istates b = none ∧ h.gzstates b = none) ∧
    (h.streams b ≠ none → h.bytes b = none ∧ h.words b = none ∧ h.gzheaders b = none ∧
        h.dstates b = none ∧ h.istates b = none ∧ h.gzstates b = none) ∧
    (h.gzheaders b ≠ none → h.bytes b = none ∧ h.words b = none ∧ h.streams b = none ∧
        h.dstates b = none ∧ h.istates b = none ∧ h.gzstates b = none) ∧
    (h.dstates b ≠ none → h.bytes b = none ∧ h.words b = none ∧ h.streams b = none ∧
        h.gzheaders b = none ∧ h.istates b = none ∧ h.gzstates b = none) ∧
    (h.istates b ≠ none → h.bytes b = none ∧ h.words b = none ∧ h.streams b = none ∧
        h.gzheaders b = none ∧ h.dstates b = none ∧ h.gzstates b = none) ∧
    (h.gzstates b ≠ none → h.bytes b = none ∧ h.words b = none ∧ h.streams b = none ∧
        h.gzheaders b = none ∧ h.dstates b = none ∧ h.istates b = none) := by
  have hub := hu b
  simp only [Zlib.Inflate.Spec.cnt] at hub
  cases hb : h.bytes b <;> cases hw : h.words b <;> cases hs : h.streams b <;>
    cases hg : h.gzheaders b <;> cases hd : h.dstates b <;> cases hi : h.istates b <;>
    cases hz : h.gzstates b <;> simp_all

private theorem streamRoot_block_live {h : Heap} {r : ZStreamRef} {z : ZStream} {b : Nat}
    (hz : r.get h = some z) (hr : StreamRoot r b) : h.live b := by
  cases r with
  | tab i =>
    cases hr
    have hst : h.streams b = some z := hz
    simp [Heap.live, hst]
  | in_gzstate_strm i =>
    cases hr
    cases hg : h.gzstates b with
    | none => simp [ZStreamRef.get, hg] at hz
    | some _ => simp [Heap.live, hg]

private theorem streamInvariant_facts {kind : StreamKind} {h : Heap} {r : ZStreamRef}
    (inv : StreamInvariant kind h r) :
    Fresh h ∧ Zlib.Inflate.Spec.Uniq h ∧ ∃ z, r.get h = some z := by
  cases kind with
  | inflate =>
    dsimp [StreamInvariant] at inv
    obtain ⟨i, z, s, good, _⟩ := inv
    exact ⟨good.fresh, good.uniq, z, good.live.hz⟩
  | deflate =>
    dsimp [StreamInvariant] at inv
    obtain ⟨i, z, d, good, _⟩ := inv
    exact ⟨good.fresh, good.uniq, z, good.live.hz⟩

private theorem streamInvariant_of_reach {kind : StreamKind} {h : Heap} {r : ZStreamRef}
    (reach : StreamReachable kind h r) : StreamInvariant kind h r := by
  cases kind with
  | inflate => exact Zlib.Inflate.Proofs.inflate_sequence_safety_public.1 h r reach
  | deflate => exact Zlib.Deflate.Universal.deflate_sequence_safety.1 h r reach

private theorem streamOwned_live {kind : StreamKind} {h : Heap} {r : ZStreamRef}
    (inv : StreamInvariant kind h r) {b : Nat} (owned : StreamOwned h r b) : h.live b := by
  rcases owned with ⟨z0, get0, hcase⟩
  cases kind with
  | inflate =>
    dsimp [StreamInvariant] at inv
    obtain ⟨i, z, s, good, _⟩ := inv
    have ez : z0 = z := Option.some.inj (get0.symm.trans good.live.hz)
    subst ez
    rcases hcase with ⟨i', s', zst, hs', hi⟩ | ⟨i', _, zst, _, _⟩
    · rw [good.live.zst] at zst; cases zst
      have es : s' = s := Option.some.inj (hs'.symm.trans good.live.hs)
      subst es
      rcases hi with rfl | hw
      · simp [Heap.live, good.live.hs]
      · rcases good.inv.win.block with hnull | ⟨w, a, ptr, bytes, _, _⟩
        · rw [hnull] at hw; cases hw
        · rw [ptr] at hw; cases hw
          simp [Heap.live, bytes]
    · rw [good.live.zst] at zst; cases zst
  | deflate =>
    dsimp [StreamInvariant] at inv
    obtain ⟨i, z, d, good, _⟩ := inv
    have ez : z0 = z := Option.some.inj (get0.symm.trans good.live.hz)
    subst ez
    rcases hcase with ⟨i', _, zst, _, _⟩ | ⟨i', d', zst, hd', hd⟩
    · rw [good.live.zst] at zst; cases zst
    · rw [good.live.zst] at zst; cases zst
      have ed : d' = d := Option.some.inj (hd'.symm.trans good.live.hs)
      subst ed
      obtain ⟨w, p, q, pb, hB⟩ := good.inv.blocks
      rcases hd with rfl | hw | hp | hq | hpb
      · simp [Heap.live, good.live.hs]
      · rw [hB.win] at hw; cases hw
        obtain ⟨a, ha, _⟩ := hB.wa; simp [Heap.live, ha]
      · rw [hB.prev] at hp; cases hp
        obtain ⟨a, ha, _⟩ := hB.pa; simp [Heap.live, ha]
      · rw [hB.head] at hq; cases hq
        obtain ⟨a, ha, _⟩ := hB.qa; simp [Heap.live, ha]
      · rw [hB.pbuf] at hpb; cases hpb
        obtain ⟨a, ha, _⟩ := hB.ba; simp [Heap.live, ha]

private theorem uniq_streamRoot_disjoint {h : Heap} {r₁ r₂ : ZStreamRef} {z₁ z₂ : ZStream}
    (hu : Zlib.Inflate.Spec.Uniq h) (hne : r₁ ≠ r₂)
    (h1 : r₁.get h = some z₁) (h2 : r₂.get h = some z₂) :
    ∀ b, StreamRoot r₁ b → ¬ StreamRoot r₂ b := by
  intro b hr1 hr2
  cases r₁ with
  | tab i₁ =>
    cases r₂ with
    | tab i₂ => cases hr1; cases hr2; exact hne rfl
    | in_gzstate_strm i₂ =>
      cases hr1; cases hr2
      cases hg : h.gzstates b with
      | none => simp [ZStreamRef.get, hg] at h2
      | some _ =>
        have hne_s : h.streams b ≠ none := by
          have e : h.streams b = some z₁ := h1
          rw [e]; exact Option.some_ne_none _
        obtain ⟨_, _, _, _, _, hgzs⟩ := (uniq_ne_none hu).2.2.1 hne_s
        rw [hg] at hgzs; exact Option.some_ne_none _ hgzs
  | in_gzstate_strm i₁ =>
    cases r₂ with
    | tab i₂ =>
      cases hr1; cases hr2
      cases hg : h.gzstates b with
      | none => simp [ZStreamRef.get, hg] at h1
      | some _ =>
        have hne_s : h.streams b ≠ none := by
          have e : h.streams b = some z₂ := h2
          rw [e]; exact Option.some_ne_none _
        obtain ⟨_, _, _, _, _, hgzs⟩ := (uniq_ne_none hu).2.2.1 hne_s
        rw [hg] at hgzs; exact Option.some_ne_none _ hgzs
    | in_gzstate_strm i₂ => cases hr1; cases hr2; exact hne rfl

private theorem uniq_streamRoot_not_streamOwned {kind : StreamKind} {h : Heap}
    {r₁ r₂ : ZStreamRef} {z₂ : ZStream}
    (inv : StreamInvariant kind h r₁) (hu : Zlib.Inflate.Spec.Uniq h)
    (hz₂ : r₂.get h = some z₂) :
    ∀ b, StreamRoot r₂ b → ¬ StreamOwned h r₁ b := by
  intro b hr2 ⟨z0, get0, hcase⟩
  have hdisj : h.istates b = none ∧ h.dstates b = none ∧ h.bytes b = none ∧ h.words b = none := by
    cases r₂ with
    | tab i =>
      cases hr2
      have hne_s : h.streams b ≠ none := by
        have e : h.streams b = some z₂ := hz₂
        rw [e]; exact Option.some_ne_none _
      obtain ⟨hb, hw, _, hd, hi, _⟩ := (uniq_ne_none hu).2.2.1 hne_s
      exact ⟨hi, hd, hb, hw⟩
    | in_gzstate_strm i =>
      cases hr2
      cases hg : h.gzstates b with
      | none => simp [ZStreamRef.get, hg] at hz₂
      | some _ =>
        have hne_g : h.gzstates b ≠ none := by rw [hg]; exact Option.some_ne_none _
        obtain ⟨hb, hw, _, _, hd, hi⟩ := (uniq_ne_none hu).2.2.2.2.2.2 hne_g
        exact ⟨hi, hd, hb, hw⟩
  cases kind with
  | inflate =>
    dsimp [StreamInvariant] at inv
    obtain ⟨i, z, s, good, _⟩ := inv
    have ez : z0 = z := Option.some.inj (get0.symm.trans good.live.hz)
    subst ez
    rcases hcase with ⟨i', s', zst, hs', hi⟩ | ⟨i', _, zst, _, _⟩
    · rw [good.live.zst] at zst; cases zst
      have es : s' = s := Option.some.inj (hs'.symm.trans good.live.hs)
      subst es
      rcases hi with rfl | hw
      · rw [good.live.hs] at hdisj; exact Option.some_ne_none _ hdisj.1
      · rcases good.inv.win.block with hnull | ⟨w, a, ptr, bytes, _, _⟩
        · rw [hnull] at hw; cases hw
        · rw [ptr] at hw; cases hw
          rw [bytes] at hdisj; exact Option.some_ne_none _ hdisj.2.2.1
    · rw [good.live.zst] at zst; cases zst
  | deflate =>
    dsimp [StreamInvariant] at inv
    obtain ⟨i, z, d, good, _⟩ := inv
    have ez : z0 = z := Option.some.inj (get0.symm.trans good.live.hz)
    subst ez
    rcases hcase with ⟨i', _, zst, _, _⟩ | ⟨i', d', zst, hd', hd⟩
    · rw [good.live.zst] at zst; cases zst
    · rw [good.live.zst] at zst; cases zst
      have ed : d' = d := Option.some.inj (hd'.symm.trans good.live.hs)
      subst ed
      obtain ⟨w, p, q, pb, hB⟩ := good.inv.blocks
      rcases hd with rfl | hw | hp | hq | hpb
      · rw [good.live.hs] at hdisj; exact Option.some_ne_none _ hdisj.2.1
      · rw [hB.win] at hw; cases hw
        obtain ⟨a, ha, _⟩ := hB.wa; rw [ha] at hdisj; exact Option.some_ne_none _ hdisj.2.2.1
      · rw [hB.prev] at hp; cases hp
        obtain ⟨a, ha, _⟩ := hB.pa; rw [ha] at hdisj; exact Option.some_ne_none _ hdisj.2.2.2
      · rw [hB.head] at hq; cases hq
        obtain ⟨a, ha, _⟩ := hB.qa; rw [ha] at hdisj; exact Option.some_ne_none _ hdisj.2.2.2
      · rw [hB.pbuf] at hpb; cases hpb
        obtain ⟨a, ha, _⟩ := hB.ba; rw [ha] at hdisj; exact Option.some_ne_none _ hdisj.2.2.1

private theorem streamHeaderRecord_gz {kind₁ : StreamKind} {h : Heap} {r₁ : ZStreamRef}
    {call : Call} {b : Nat}
    (op : StreamOperation kind₁ r₁ call) (args : StreamArguments h r₁ call)
    (hdr : StreamHeaderRecord h r₁ call b) :
    ∃ g, h.gzheaders b = some g := by
  rcases hdr with hget | ⟨z, i, s, hz, zst, hs, head, flush, hinf_call⟩
  · subst call
    dsimp [StreamOperation] at op
    obtain ⟨hkind, _⟩ := op
    subst hkind
    dsimp [StreamArguments] at args
    rcases args.1 with hnone | ⟨j, g, eq, hget, _⟩
    · cases hnone
    · cases eq; exact ⟨g, hget⟩
  · subst call
    dsimp [StreamOperation] at op
    obtain ⟨hkind, _⟩ := op
    subst hkind
    dsimp [StreamArguments] at args
    obtain ⟨z', hz', hinf, _⟩ := args.2
    have ez : z' = z := Option.some.inj (hz'.symm.trans hz)
    subst ez
    have hmem := hinf i s zst hs
    rcases hmem.1 with hnone | ⟨j, g, eq, hget, _⟩
    · rw [head] at hnone; cases hnone
    · rw [head] at eq; cases eq; exact ⟨g, hget⟩

private theorem uniq_gzheader_not_other {kind₂ : StreamKind} {h : Heap} {r₂ : ZStreamRef}
    (inv₂ : StreamInvariant kind₂ h r₂) (hu : Zlib.Inflate.Spec.Uniq h)
    {b : Nat} {g : GzHeader} (hgz : h.gzheaders b = some g) :
    ¬ StreamRoot r₂ b ∧ ¬ StreamOwned h r₂ b := by
  have hne : h.gzheaders b ≠ none := by rw [hgz]; exact Option.some_ne_none _
  obtain ⟨hby, hwo, hst, hds, his, hgzs⟩ := (uniq_ne_none hu).2.2.2.1 hne
  constructor
  · intro hr2
    obtain ⟨_, _, ⟨z₂, hz₂⟩⟩ := streamInvariant_facts inv₂
    cases r₂ with
    | tab i =>
      cases hr2
      have e : h.streams b = some z₂ := hz₂
      rw [e] at hst; exact Option.some_ne_none _ hst
    | in_gzstate_strm i =>
      cases hr2
      cases hg : h.gzstates b with
      | none => simp [ZStreamRef.get, hg] at hz₂
      | some _ => rw [hg] at hgzs; exact Option.some_ne_none _ hgzs
  · intro ⟨z0, get0, hcase⟩
    cases kind₂ with
    | inflate =>
      dsimp [StreamInvariant] at inv₂
      obtain ⟨i, z, s, good, _⟩ := inv₂
      have ez : z0 = z := Option.some.inj (get0.symm.trans good.live.hz)
      subst ez
      rcases hcase with ⟨i', s', zst, hs', hi⟩ | ⟨i', _, zst, _, _⟩
      · rw [good.live.zst] at zst; cases zst
        have es : s' = s := Option.some.inj (hs'.symm.trans good.live.hs)
        subst es
        rcases hi with rfl | hw
        · rw [good.live.hs] at his; exact Option.some_ne_none _ his
        · rcases good.inv.win.block with hnull | ⟨w, a, ptr, bytes, _, _⟩
          · rw [hnull] at hw; cases hw
          · rw [ptr] at hw; cases hw
            rw [bytes] at hby; exact Option.some_ne_none _ hby
      · rw [good.live.zst] at zst; cases zst
    | deflate =>
      dsimp [StreamInvariant] at inv₂
      obtain ⟨i, z, d, good, _⟩ := inv₂
      have ez : z0 = z := Option.some.inj (get0.symm.trans good.live.hz)
      subst ez
      rcases hcase with ⟨i', _, zst, _, _⟩ | ⟨i', d', zst, hd', hd⟩
      · rw [good.live.zst] at zst; cases zst
      · rw [good.live.zst] at zst; cases zst
        have ed : d' = d := Option.some.inj (hd'.symm.trans good.live.hs)
        subst ed
        obtain ⟨w, p, q, pb, hB⟩ := good.inv.blocks
        rcases hd with rfl | hw | hp | hq | hpb
        · rw [good.live.hs] at hds; exact Option.some_ne_none _ hds
        · rw [hB.win] at hw; cases hw
          obtain ⟨a, ha, _⟩ := hB.wa; rw [ha] at hby; exact Option.some_ne_none _ hby
        · rw [hB.prev] at hp; cases hp
          obtain ⟨a, ha, _⟩ := hB.pa; rw [ha] at hwo; exact Option.some_ne_none _ hwo
        · rw [hB.head] at hq; cases hq
          obtain ⟨a, ha, _⟩ := hB.qa; rw [ha] at hwo; exact Option.some_ne_none _ hwo
        · rw [hB.pbuf] at hpb; cases hpb
          obtain ⟨a, ha, _⟩ := hB.ba; rw [ha] at hby; exact Option.some_ne_none _ hby

private def restoreStep (before current : Heap) (reg : Region) : Heap :=
  match reg.pointer with
  | .null => current
  | .ref r _ => match Space.get before r with
    | none => current
    | some a => Space.put current r a

private theorem restoreStep_tables_other (before current : Heap) (reg : Region) :
    (restoreStep before current reg).static = current.static ∧
    (restoreStep before current reg).allocOk = current.allocOk ∧
    (restoreStep before current reg).garbage = current.garbage ∧
    (restoreStep before current reg).nextBlk = current.nextBlk ∧
    (restoreStep before current reg).nalloc = current.nalloc ∧
    (restoreStep before current reg).words = current.words ∧
    (restoreStep before current reg).streams = current.streams ∧
    (restoreStep before current reg).gzheaders = current.gzheaders ∧
    (restoreStep before current reg).istates = current.istates ∧
    (restoreStep before current reg).gzstates = current.gzstates ∧
    (restoreStep before current reg).ro = current.ro := by
  dsimp [restoreStep]
  rcases reg with ⟨ptr, len⟩
  cases ptr with
  | null => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | ref ref off =>
    cases hget : Space.get before ref with
    | none => simp [hget]
    | some a =>
      cases ref with
      | blk k => simp [Space.put, hget]
      | str _ => simp [Space.put, hget]
      | st_dist_code => simp [Space.put, hget]
      | st_length_code => simp [Space.put, hget]
      | dstate_depth k =>
        simp only [Space.put]
        cases current.dstates k <;> simp [hget]

private theorem restoreRegions_tables_other (before after : Heap) (regs : List Region) :
    (restoreRegions before after regs).static = after.static ∧
    (restoreRegions before after regs).allocOk = after.allocOk ∧
    (restoreRegions before after regs).garbage = after.garbage ∧
    (restoreRegions before after regs).nextBlk = after.nextBlk ∧
    (restoreRegions before after regs).nalloc = after.nalloc ∧
    (restoreRegions before after regs).words = after.words ∧
    (restoreRegions before after regs).streams = after.streams ∧
    (restoreRegions before after regs).gzheaders = after.gzheaders ∧
    (restoreRegions before after regs).istates = after.istates ∧
    (restoreRegions before after regs).gzstates = after.gzstates ∧
    (restoreRegions before after regs).ro = after.ro := by
  induction regs generalizing after with
  | nil => simp [restoreRegions]
  | cons reg rest ih =>
    change (restoreRegions before (restoreStep before after reg) rest).static = after.static ∧ _
    have hs := restoreStep_tables_other before after reg
    have ih' := ih (restoreStep before after reg)
    exact ⟨ih'.1.trans hs.1, ih'.2.1.trans hs.2.1, ih'.2.2.1.trans hs.2.2.1,
      ih'.2.2.2.1.trans hs.2.2.2.1, ih'.2.2.2.2.1.trans hs.2.2.2.2.1,
      ih'.2.2.2.2.2.1.trans hs.2.2.2.2.2.1, ih'.2.2.2.2.2.2.1.trans hs.2.2.2.2.2.2.1,
      ih'.2.2.2.2.2.2.2.1.trans hs.2.2.2.2.2.2.2.1, ih'.2.2.2.2.2.2.2.2.1.trans hs.2.2.2.2.2.2.2.2.1,
      ih'.2.2.2.2.2.2.2.2.2.1.trans hs.2.2.2.2.2.2.2.2.2.1, ih'.2.2.2.2.2.2.2.2.2.2.trans hs.2.2.2.2.2.2.2.2.2.2⟩

private theorem restoreRegions_preserve_at (before after : Heap) (regs : List Region) {b : Nat}
    (hnone : ∀ reg ∈ regs, ¬ ByteRoot reg.pointer b) :
    (restoreRegions before after regs).bytes b = after.bytes b ∧
    (restoreRegions before after regs).dstates b = after.dstates b := by
  induction regs generalizing after with
  | nil => simp [restoreRegions]
  | cons reg rest ih =>
    change (restoreRegions before (restoreStep before after reg) rest).bytes b = after.bytes b ∧
      (restoreRegions before (restoreStep before after reg) rest).dstates b = after.dstates b
    have hthis : ¬ ByteRoot reg.pointer b := hnone reg (by simp)
    have hrest : ∀ r' ∈ rest, ¬ ByteRoot r'.pointer b := fun r' hr' => hnone r' (by simp [hr'])
    have hmid : (restoreStep before after reg).bytes b = after.bytes b ∧
        (restoreStep before after reg).dstates b = after.dstates b := by
      dsimp [restoreStep]
      rcases reg with ⟨ptr, len⟩
      cases ptr with
      | null => exact ⟨rfl, rfl⟩
      | ref ref off =>
        cases hget : Space.get before ref with
        | none => simp [hget]
        | some a =>
          cases ref with
          | blk k =>
            have hne : b ≠ k := hthis
            simp [Space.put, hget, upd_ne _ _ _ _ hne]
          | dstate_depth k =>
            have hne : b ≠ k := hthis
            simp only [Space.put]
            cases after.dstates k <;> simp [hget, upd_ne _ _ _ _ hne]
          | str _ => simp [Space.put, hget]
          | st_dist_code => simp [Space.put, hget]
          | st_length_code => simp [Space.put, hget]
    have ih' := ih (restoreStep before after reg) hrest
    exact ⟨ih'.1.trans hmid.1, ih'.2.trans hmid.2⟩

private theorem frame_of_restore_step {h after : Heap} {r₂ : ZStreamRef} {kind₂ : StreamKind}
    {changed : Nat → Prop} {regs : List Region}
    (inv₂ : StreamInvariant kind₂ h r₂)
    (bframe : BufferFrame h after changed regs)
    (noRoot : ∀ b, StreamRoot r₂ b → ¬ changed b)
    (noOwn : ∀ b, StreamOwned h r₂ b → ¬ changed b)
    (noExt : ∀ reg ∈ regs, ∀ b, ByteRoot reg.pointer b → ¬ StreamOwned h r₂ b) :
    r₂.get after = r₂.get h ∧
    Frame h after (fun b => ¬ StreamOwned h r₂ b) := by
  obtain ⟨⟨hstat, haok, hgar, hnb, hna, hkeep⟩, _⟩ := bframe
  have htab := restoreRegions_tables_other h after regs
  obtain ⟨_, _, ⟨z₂, hz₂⟩⟩ := streamInvariant_facts inv₂
  have hroot_eq : r₂.get after = r₂.get h := by
    cases r₂ with
    | tab b₂ =>
      have hlive : h.live b₂ := streamRoot_block_live hz₂ rfl
      have hk := hkeep b₂ hlive (noRoot b₂ rfl)
      have hst : after.streams b₂ = h.streams b₂ := by
        have e := hk.2.2.1; rw [htab.2.2.2.2.2.2.1] at e; exact e
      exact hst
    | in_gzstate_strm b₂ =>
      have hlive : h.live b₂ := streamRoot_block_live hz₂ rfl
      have hk := hkeep b₂ hlive (noRoot b₂ rfl)
      have hgz : after.gzstates b₂ = h.gzstates b₂ := by
        have e := hk.2.2.2.2.2.2.1; rw [htab.2.2.2.2.2.2.2.2.2.1] at e; exact e
      exact congrArg (Option.map (·.strm)) hgz
  refine ⟨hroot_eq, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← htab.1]; exact hstat
  · rw [← htab.2.1]; exact haok
  · rw [← htab.2.2.1]; exact hgar
  · rw [← htab.2.2.2.1]; exact hnb
  · rw [← htab.2.2.2.2.1]; exact hna
  · intro b hlive hnot
    have hown : StreamOwned h r₂ b := Classical.byContradiction hnot
    have hk := hkeep b hlive (noOwn b hown)
    have hbd := restoreRegions_preserve_at h after regs (fun reg hreg hbr => noExt reg hreg b hbr hown)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hbd.1]; exact hk.1
    · rw [← htab.2.2.2.2.2.1]; exact hk.2.1
    · rw [← htab.2.2.2.2.2.2.1]; exact hk.2.2.1
    · rw [← htab.2.2.2.2.2.2.2.1]; exact hk.2.2.2.1
    · rw [← hbd.2]; exact hk.2.2.2.2.1
    · rw [← htab.2.2.2.2.2.2.2.2.1]; exact hk.2.2.2.2.2.1
    · rw [← htab.2.2.2.2.2.2.2.2.2.1]; exact hk.2.2.2.2.2.2.1
    · rw [← htab.2.2.2.2.2.2.2.2.2.2]; exact hk.2.2.2.2.2.2.2

private theorem streamOwned_of_frame_other {h after : Heap} {r₂ : ZStreamRef}
    (hr₂ : r₂.get after = r₂.get h)
    (hframe : Frame h after (fun b => ¬ StreamOwned h r₂ b))
    (inv₂ : ∀ kind, StreamInvariant kind h r₂ → ∀ b, StreamOwned h r₂ b → h.live b) :
    ∀ kind, StreamInvariant kind h r₂ → ∀ b, StreamOwned after r₂ b ↔ StreamOwned h r₂ b := by
  intro kind hInv b
  have hkeep := hframe.2.2.2.2.2
  constructor
  · intro ⟨z', get', hcase⟩
    have hroot : ∃ z, r₂.get h = some z := (streamInvariant_facts hInv).2.2
    obtain ⟨z₀, hz₀⟩ := hroot
    have ez' : z' = z₀ := Option.some.inj (get'.symm.trans (hr₂.trans hz₀))
    subst z'
    rcases hcase with ⟨i', s', zst, hs', hi⟩ | ⟨i', d', zst, hd', hd⟩
    · cases kind with
      | inflate =>
        dsimp [StreamInvariant] at hInv
        obtain ⟨i, z, s, good, _⟩ := hInv
        have ez : z₀ = z := Option.some.inj (hz₀.symm.trans good.live.hz)
        subst z₀
        rw [good.live.zst] at zst
        have ei : i' = i := by cases zst; rfl
        subst i'
        have hs0 : after.istates i = h.istates i :=
          (hkeep i (by simp [Heap.live, good.live.hs])
            (fun hno => hno ⟨z, good.live.hz, Or.inl ⟨i, s, good.live.zst, good.live.hs, Or.inl rfl⟩⟩)).2.2.2.2.2.1
        rw [hs0] at hs'
        have es : s' = s := Option.some.inj (hs'.symm.trans good.live.hs)
        subst s'
        exact ⟨z, good.live.hz, Or.inl ⟨i, s, good.live.zst, good.live.hs, hi⟩⟩
      | deflate =>
        dsimp [StreamInvariant] at hInv
        obtain ⟨i, z, d, good, _⟩ := hInv
        have ez : z₀ = z := Option.some.inj (hz₀.symm.trans good.live.hz)
        subst z₀
        rw [good.live.zst] at zst; cases zst
    · cases kind with
      | inflate =>
        dsimp [StreamInvariant] at hInv
        obtain ⟨i, z, s, good, _⟩ := hInv
        have ez : z₀ = z := Option.some.inj (hz₀.symm.trans good.live.hz)
        subst z₀
        rw [good.live.zst] at zst; cases zst
      | deflate =>
        dsimp [StreamInvariant] at hInv
        obtain ⟨i, z, d, good, _⟩ := hInv
        have ez : z₀ = z := Option.some.inj (hz₀.symm.trans good.live.hz)
        subst z₀
        rw [good.live.zst] at zst
        have ei : i' = i := by cases zst; rfl
        subst i'
        have hd0 : after.dstates i = h.dstates i :=
          (hkeep i (by simp [Heap.live, good.live.hs])
            (fun hno => hno ⟨z, good.live.hz, Or.inr ⟨i, d, good.live.zst, good.live.hs, Or.inl rfl⟩⟩)).2.2.2.2.1
        rw [hd0] at hd'
        have ed : d' = d := Option.some.inj (hd'.symm.trans good.live.hs)
        subst d'
        exact ⟨z, good.live.hz, Or.inr ⟨i, d, good.live.zst, good.live.hs, hd⟩⟩
  · intro hown
    have _hk := hkeep b (inv₂ kind hInv b hown) (fun hno => hno hown)
    rcases hown with ⟨z, hz, hcase⟩
    refine ⟨z, hr₂.trans hz, ?_⟩
    rcases hcase with ⟨i, s, zst, hs, hi⟩ | ⟨i, d, zst, hd, hd_own⟩
    · left
      have hlive_i : h.live i := by simp [Heap.live, hs]
      have hown_i : StreamOwned h r₂ i := ⟨z, hz, Or.inl ⟨i, s, zst, hs, Or.inl rfl⟩⟩
      have hki := (hkeep i hlive_i (fun hno => hno hown_i)).2.2.2.2.2.1
      refine ⟨i, s, zst, hki.trans hs, hi⟩
    · right
      have hlive_i : h.live i := by simp [Heap.live, hd]
      have hown_i : StreamOwned h r₂ i := ⟨z, hz, Or.inr ⟨i, d, zst, hd, Or.inl rfl⟩⟩
      have hki := (hkeep i hlive_i (fun hno => hno hown_i)).2.2.2.2.1
      refine ⟨i, d, zst, hki.trans hd, hd_own⟩

private theorem rebuffer_of_step_frame {h after : Heap} {r₂ : ZStreamRef} {kind₂ : StreamKind}
    {changed : Nat → Prop} {regs : List Region}
    (reach₂ : StreamReachable kind₂ h r₂)
    (inv₂ : StreamInvariant kind₂ h r₂)
    (freshAfter : Fresh after)
    (uniqAfter : Zlib.Inflate.Spec.Uniq after)
    (globalsAfter : LibraryGlobals after)
    (bframe : BufferFrame h after changed regs)
    (noRoot : ∀ b, StreamRoot r₂ b → ¬ changed b)
    (noOwn : ∀ b, StreamOwned h r₂ b → ¬ changed b)
    (noExt : ∀ reg ∈ regs, ∀ b, ByteRoot reg.pointer b → ¬ StreamOwned h r₂ b) :
    Rebuffer h after r₂ ∧ r₂.get after = r₂.get h ∧
    (∀ b, StreamOwned after r₂ b ↔ StreamOwned h r₂ b) ∧
    ((kind₂ = .inflate → ZlibF.PlatformMemory.ByteObjectsFit after) →
      StreamReachable kind₂ after r₂ ∧ StreamInvariant kind₂ after r₂) := by
  obtain ⟨hr₂, hframe⟩ := frame_of_restore_step inv₂ bframe noRoot noOwn noExt
  obtain ⟨_, _, ⟨z₂, hz₂⟩⟩ := streamInvariant_facts inv₂
  have hreb : Rebuffer h after r₂ := by
    refine ⟨freshAfter, uniqAfter, globalsAfter, hframe, z₂, z₂, hz₂, hr₂.trans hz₂, ?_⟩
    cases z₂; rfl
  have hown : ∀ b, StreamOwned after r₂ b ↔ StreamOwned h r₂ b :=
    streamOwned_of_frame_other hr₂ hframe (fun _ hi _ ho => streamOwned_live hi ho) kind₂ inv₂
  refine ⟨hreb, hr₂, hown, fun hfit => ?_⟩
  have reach' : StreamReachable kind₂ after r₂ := StreamReachable.rebuffer reach₂ hreb hfit
  have inv' : StreamInvariant kind₂ after r₂ := streamInvariant_of_reach reach'
  exact ⟨reach', inv'⟩

private theorem streamInvariant_of_frame_other {kind : StreamKind} {h after : Heap} {r₂ : ZStreamRef}
    (inv₂ : StreamInvariant kind h r₂)
    (hr₂ : r₂.get after = r₂.get h)
    (hframe : Frame h after (fun b => ¬ StreamOwned h r₂ b))
    (freshAfter : Fresh after)
    (uniqAfter : Zlib.Inflate.Spec.Uniq after) :
    StreamInvariant kind after r₂ := by
  have hkeep := hframe.2.2.2.2.2
  cases kind with
  | inflate =>
    dsimp [StreamInvariant] at inv₂ ⊢
    obtain ⟨i, z, s, good, dalloc⟩ := inv₂
    have hown_i : StreamOwned h r₂ i := ⟨z, good.live.hz, Or.inl ⟨i, s, good.live.zst, good.live.hs, Or.inl rfl⟩⟩
    have hki := hkeep i (by simp [Heap.live, good.live.hs]) (fun hno => hno hown_i)
    have hwin : Zlib.Inflate.Spec.WinInv after s := by
      refine ⟨good.inv.win.wbits, ?_, good.inv.win.nullws, good.inv.win.ws, good.inv.win.hv, good.inv.win.wn, good.inv.win.eq⟩
      rcases good.inv.win.block with hnull | ⟨w, a, ptr, bytes, ro, size⟩
      · exact Or.inl hnull
      · right
        have hown_w : StreamOwned h r₂ w := ⟨z, good.live.hz, Or.inl ⟨i, s, good.live.zst, good.live.hs, Or.inr ptr⟩⟩
        have hkw := hkeep w (by simp [Heap.live, bytes]) (fun hno => hno hown_w)
        exact ⟨w, a, ptr, hkw.1.trans bytes, hkw.2.2.2.2.2.2.2.trans ro, size⟩
    refine ⟨i, z, s, ⟨⟨hr₂.trans good.live.hz, hki.2.2.2.2.2.1.trans good.live.hs, good.live.zst,
      good.live.back, good.live.mode, good.live.zalloc, good.live.zfree⟩,
      { good.inv with win := hwin }, uniqAfter, freshAfter⟩, dalloc⟩
  | deflate =>
    dsimp [StreamInvariant] at inv₂ ⊢
    obtain ⟨i, z, d, good, dalloc⟩ := inv₂
    have hown_i : StreamOwned h r₂ i := ⟨z, good.live.hz, Or.inr ⟨i, d, good.live.zst, good.live.hs, Or.inl rfl⟩⟩
    have hki := hkeep i (by simp [Heap.live, good.live.hs]) (fun hno => hno hown_i)
    obtain ⟨w, p, q, pb, hB⟩ := good.inv.blocks
    have hown_w : StreamOwned h r₂ w := ⟨z, good.live.hz, Or.inr ⟨i, d, good.live.zst, good.live.hs, Or.inr (Or.inl hB.win)⟩⟩
    have hown_p : StreamOwned h r₂ p := ⟨z, good.live.hz, Or.inr ⟨i, d, good.live.zst, good.live.hs, Or.inr (Or.inr (Or.inl hB.prev))⟩⟩
    have hown_q : StreamOwned h r₂ q := ⟨z, good.live.hz, Or.inr ⟨i, d, good.live.zst, good.live.hs, Or.inr (Or.inr (Or.inr (Or.inl hB.head)))⟩⟩
    have hown_b : StreamOwned h r₂ pb := ⟨z, good.live.hz, Or.inr ⟨i, d, good.live.zst, good.live.hs, Or.inr (Or.inr (Or.inr (Or.inr hB.pbuf)))⟩⟩
    obtain ⟨wa, hwa, wsz⟩ := hB.wa
    obtain ⟨pa, hpa, psz⟩ := hB.pa
    obtain ⟨qa, hqa, qsz⟩ := hB.qa
    obtain ⟨ba, hba, bsz⟩ := hB.ba
    have hkw := hkeep w (by simp [Heap.live, hwa]) (fun hno => hno hown_w)
    have hkp := hkeep p (by simp [Heap.live, hpa]) (fun hno => hno hown_p)
    have hkq := hkeep q (by simp [Heap.live, hqa]) (fun hno => hno hown_q)
    have hkb := hkeep pb (by simp [Heap.live, hba]) (fun hno => hno hown_b)
    have htrees : Zlib.Trees.Proofs.Out.TreesInv after i := by
      have ⟨d0, b0, buf0, htr⟩ := good.trees
      have e0 : d0 = d := Option.some.inj (htr.base.dstate.symm.trans good.live.hs)
      subst d0
      have hpbuf : b0 = pb := by
        have e1 : d.pending_buf = .ref (.blk b0) 0 := htr.base.pbuf
        have e2 : d.pending_buf = .ref (.blk pb) 0 := hB.pbuf
        rw [e1] at e2; cases e2; rfl
      subst b0
      refine ⟨d, pb, buf0, { htr with
        base := { htr.base with
          static := by rw [← hframe.1]; exact htr.base.static
          dstate := hki.2.2.2.2.1.trans htr.base.dstate
          bytes := hkb.1.trans htr.base.bytes
          rw := hkb.2.2.2.2.2.2.2.trans htr.base.rw } }⟩
    have hB' : Zlib.Deflate.Spec.DBlocks after d w p q pb :=
      { hB with
        wa := ⟨wa, hkw.1.trans hwa, wsz⟩
        wro := hkw.2.2.2.2.2.2.2.trans hB.wro
        pa := ⟨pa, hkp.2.1.trans hpa, psz⟩
        qa := ⟨qa, hkq.2.1.trans hqa, qsz⟩
        ba := ⟨ba, hkb.1.trans hba, bsz⟩
        bro := hkb.2.2.2.2.2.2.2.trans hB.bro }
    exact ⟨i, z, d, ⟨⟨hr₂.trans good.live.hz, hki.2.2.2.2.1.trans good.live.hs, good.live.zst,
      good.live.back, good.live.status, good.live.zalloc, good.live.zfree⟩,
      { good.inv with blocks := ⟨w, p, q, pb, hB'⟩ }, uniqAfter, freshAfter, htrees⟩, dalloc⟩

private theorem inflate_owned_eq {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (good : Zlib.Inflate.Spec.Good h r zs z s) (b : Nat) :
    StreamOwned h r b ↔ b = zs ∨ s.window = .ref (.blk b) 0 :=
  good.streamOwned_iff b

private theorem inflate_op_owned_within
    {h after : Heap} {r₁ : ZStreamRef} {zs : Nat} {z₁ : ZStream} {s₁ : InflateState}
    {call : Call} {val : call.Result}
    (inv₁ : Zlib.Inflate.Proofs.InflateInv h r₁ zs z₁ s₁)
    (held₁ : Zlib.Inflate.Proofs.DecoderHeldBits s₁)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (op : StreamOperation .inflate r₁ call)
    (args : StreamArguments h r₁ call)
    (run : call.execute default h = .ok ((val, default), after)) :
    ∀ b, StreamOwned after r₁ b → StreamOwned h r₁ b ∨ ¬ h.live b := by
  have good₁ := inv₁.good
  cases call with
  | inflate p flush =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    have hrun : Zlib.Inflate.inflate (some r₁) flush h = .ok (val, after) :=
      Zlib.Inflate.Proofs.run_of_heapCall run
    have hpres := Zlib.Inflate.Proofs.inflate_preserves r₁ flush h after zs z₁ s₁ val inv₁ held₁ platform args run
    obtain ⟨z', s', inv', _⟩ := hpres
    have kc := Zlib.Inflate.KeepProofs.call_inflate (some r₁) flush h val after hrun
    obtain ⟨s₀, hs₀, ctl⟩ := kc.states zs s' inv'.good.live.hs
    have es₀ : s₀ = s₁ := Option.some.inj (hs₀.symm.trans good₁.live.hs)
    subst es₀
    intro b hown
    rw [inflate_owned_eq inv'.good b] at hown
    rcases hown with rfl | hwin
    · left; rw [inflate_owned_eq good₁]; exact Or.inl rfl
    · rcases ctl.fresh with hsame | ⟨w, hw, hnb⟩
      · left; rw [inflate_owned_eq good₁]; right; rw [← hsame]; exact hwin
      · rw [hw] at hwin; cases hwin
        right; exact good₁.fresh b hnb
  | inflateReset p =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    have hrun : C.run (Zlib.Inflate.inflateReset (some r₁)) h = .ok (val, after) :=
      Zlib.Inflate.Proofs.run_of_heapCall run
    obtain ⟨h', run', _, good', _⟩ := Zlib.Inflate.Proofs.inflateReset_safe good₁ inv₁.alloc.2
    have hsame := Except.ok.inj (hrun.symm.trans run')
    cases hsame
    intro b hown
    rw [inflate_owned_eq good' b] at hown
    left; rw [inflate_owned_eq good₁ b]
    rcases hown with rfl | hwin
    · exact Or.inl rfl
    · right
      dsimp only [Zlib.Inflate.Spec.resetKeepState, Zlib.Inflate.Spec.resetPre] at hwin
      cases hne : (s₁.wbits != s₁.reqbits) <;> simp [hne] at hwin
      exact hwin
  | inflateReset2 p wb =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    have hrun : C.run (Zlib.Inflate.inflateReset2 (some r₁) wb) h = .ok (val, after) :=
      Zlib.Inflate.Proofs.run_of_heapCall run
    obtain ⟨code, h', run', res⟩ := Zlib.Inflate.Proofs.inflateReset2_safe good₁ inv₁.alloc.2 wb
    cases hp : Zlib.Inflate.Spec.reset2Params wb with
    | none =>
      rw [hp] at res
      obtain ⟨_, rfl⟩ := res
      have hsame := Except.ok.inj (hrun.symm.trans run')
      cases hsame
      exact fun b hown => Or.inl hown
    | some selected =>
      obtain ⟨wrap, width⟩ := selected
      rw [hp] at res
      obtain ⟨_, _, good', _⟩ := res
      have hsame := Except.ok.inj (hrun.symm.trans run')
      cases hsame
      intro b hown
      rw [inflate_owned_eq good' b] at hown
      left; rw [inflate_owned_eq good₁ b]
      rcases hown with rfl | hwin
      · exact Or.inl rfl
      · right
        dsimp only [Zlib.Inflate.Spec.resetKeepState, Zlib.Inflate.Spec.resetPre,
          Zlib.Inflate.Spec.reset2Pre] at hwin
        cases hne : (s₁.wbits != Zlib.Inflate.i2u width) <;> simp [hne] at hwin
        exact hwin
  | inflateResetKeep p =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    have hrun : C.run (Zlib.Inflate.inflateResetKeep (some r₁)) h = .ok (val, after) :=
      Zlib.Inflate.Proofs.run_of_heapCall run
    obtain ⟨h', run', _, good', _⟩ := Zlib.Inflate.Proofs.inflateResetKeep_safe good₁
    have hsame := Except.ok.inj (hrun.symm.trans run')
    cases hsame
    intro b hown
    rw [inflate_owned_eq good' b] at hown
    left; rw [inflate_owned_eq good₁ b]
    exact hown
  | inflatePrime p bits word =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    have hrun : C.run (Zlib.Inflate.inflatePrime (some r₁) bits word) h = .ok (val, after) :=
      Zlib.Inflate.Proofs.run_of_heapCall run
    obtain ⟨zero, clear, reject, insert⟩ := Zlib.Inflate.Proofs.inflatePrime_spec good₁ bits word
    by_cases equal : bits = 0
    · cases Except.ok.inj (hrun.symm.trans (zero equal))
      exact fun _ => Or.inl
    by_cases negative : bits < 0
    · obtain ⟨run', good'⟩ := clear negative
      cases Except.ok.inj (hrun.symm.trans run')
      intro b hown
      rw [inflate_owned_eq good' b] at hown
      left; rw [inflate_owned_eq good₁ b]; exact hown
    have positive : 0 < bits := by
      rw [Int32.lt_iff_toInt_lt] at negative ⊢
      have nz : bits.toInt ≠ 0 := fun e => equal (Int32.toInt_inj.mp e)
      simp only [Int32.toInt_zero] at negative ⊢; omega
    by_cases wide : 16 < bits.toInt
    · cases Except.ok.inj (hrun.symm.trans (reject positive (Or.inl wide)))
      exact fun _ => Or.inl
    by_cases full : 32 < s₁.bits.toNat + bits.toInt.toNat
    · cases Except.ok.inj (hrun.symm.trans (reject positive (Or.inr full)))
      exact fun _ => Or.inl
    obtain ⟨run', good'⟩ := insert positive (by omega) (by omega)
    cases Except.ok.inj (hrun.symm.trans run')
    intro b hown
    rw [inflate_owned_eq good' b] at hown
    left; rw [inflate_owned_eq good₁ b]; exact hown
  | inflateGetDictionary p dest dl =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    have hrun : C.run (Zlib.Inflate.inflateGetDictionary (some r₁) dest dl) h = .ok (val, after) :=
      Zlib.Inflate.Proofs.run_of_heapCall run
    by_cases empty : dest = .null ∨ s₁.whave = 0
    · have actual : C.run (Zlib.Inflate.inflateGetDictionary (some r₁) dest dl) h =
          .ok ((Z_OK, dl.map (fun _ => s₁.whave)), h) := by
        unfold C.run Zlib.Inflate.inflateGetDictionary
        rcases empty with null | zero
        · cases dl <;> simp [Zlib.Inflate.Proofs.stateCheck_live good₁.live,
            Zlib.Inflate.Proofs.ldZ_eq, Zlib.Inflate.Proofs.ldI_eq,
            good₁.live.hz, good₁.live.zst, Zlib.Inflate.Proofs.castI, good₁.live.hs, null]
        · cases dl <;> simp [Zlib.Inflate.Proofs.stateCheck_live good₁.live,
            Zlib.Inflate.Proofs.ldZ_eq, Zlib.Inflate.Proofs.ldI_eq,
            good₁.live.hz, good₁.live.zst, Zlib.Inflate.Proofs.castI, good₁.live.hs, zero]
      cases Except.ok.inj (hrun.symm.trans actual)
      exact fun _ => Or.inl
    · have nonnull : dest ≠ .null := fun e => empty (Or.inl e)
      have positive : s₁.whave ≠ 0 := fun e => empty (Or.inr e)
      have positiveNat : 0 < s₁.whave.toNat := by
        have : s₁.whave.toNat ≠ 0 := fun e => positive (UInt32.toNat_inj.mp (by simpa using e))
        omega
      obtain ⟨w, a, window, bytes, _, size⟩ :
          ∃ w a, s₁.window = .ref (.blk w) 0 ∧ h.bytes w = some a ∧
            h.ro w = false ∧ a.size = 2 ^ s₁.wbits.toNat := by
        rcases good₁.inv.win.block with null | blk
        · have := good₁.inv.win.nullws null
          have := good₁.inv.win.hv
          simp_all
        · exact blk
      have bounded : s₁.whave.toNat ≤ a.size := by
        have := good₁.inv.win.hv
        rcases good₁.inv.win.ws with z0 | ws <;> omega
      have chronological : s₁.wnext.toNat ≤ s₁.whave.toNat := by
        rcases Nat.lt_or_ge s₁.whave.toNat s₁.wsize.toNat with growing | full
        · have := good₁.inv.win.eq growing; omega
        · have := good₁.inv.win.wn; have := good₁.inv.win.hv; omega
      obtain ⟨stream, index, state, streamGet, pointer, stateGet, range⟩ := args
      have sameStream : stream = z₁ := Option.some.inj (streamGet.symm.trans good₁.live.hz)
      subst stream
      have sameIndex : index = zs := by rw [good₁.live.zst] at pointer; cases pointer; rfl
      subst index
      have sameState : state = s₁ := Option.some.inj (stateGet.symm.trans good₁.live.hs)
      subst state
      have writable : Writable h dest s₁.whave.toNat := by
        rcases range with null | ⟨_, write⟩
        · exact absurd null nonnull
        · exact write.1 rfl
      rcases writable with ⟨null, _⟩ | ⟨ref, off, old, pointer, get, write, room⟩
      · exact absurd null nonnull
      · have separate := Zlib.Inflate.Proofs.callerRange_private_window good₁ range pointer
        have actual := Zlib.Inflate.Proofs.inflateGetDictionary_copy_general (dl := dl) good₁.live window bytes get write
          (separate w window) positive chronological bounded room
        have run' : C.run (Zlib.Inflate.inflateGetDictionary (some r₁) dest dl) h =
            .ok ((Z_OK, dl.map (fun _ => s₁.whave)), Space.put h ref (Zlib.Inflate.Spec.getDictBytes old a off s₁.wnext.toNat s₁.whave.toNat)) := by
          simpa only [C.run, pointer] using actual
        cases Except.ok.inj (hrun.symm.trans run')
        have currentGood := good₁.byte_view_put get write separate
          (Zlib.Inflate.Spec.getDictBytes old a off s₁.wnext.toNat s₁.whave.toNat)
        intro b hown
        rw [inflate_owned_eq currentGood b] at hown
        left; rw [inflate_owned_eq good₁ b]; exact hown
  | inflateSetDictionary p src len =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    have hrun : C.run (Zlib.Inflate.inflateSetDictionary (some r₁) src len) h = .ok (val, after) :=
      Zlib.Inflate.Proofs.run_of_heapCall run
    obtain ⟨z', state, next, _⟩ :=
      Zlib.Inflate.Proofs.inflateSetDictionary_preserves r₁ src len h after zs z₁ s₁ val inv₁ platform args run
    by_cases refused : src = .null ∨ (s₁.wrap ≠ 0 ∧ s₁.mode ≠ DICT)
    · have actual := Zlib.Inflate.Proofs.inflateSetDictionary_refused_any good₁.live src len refused
      cases Except.ok.inj (hrun.symm.trans actual)
      exact fun _ => Or.inl
    · have nonnull : src ≠ .null := fun e => refused (Or.inl e)
      have allowed : s₁.wrap = 0 ∨ s₁.mode = DICT := by
        by_cases raw : s₁.wrap = 0
        · exact Or.inl raw
        · right
          exact Classical.byContradiction fun wrong => refused (Or.inr ⟨raw, wrong⟩)
      obtain ⟨xs, readable⟩ := args.resolve_left nonnull |>.1
      rcases readable with null | ⟨ref, off, array, pointer, get, room, _⟩
      · exact (nonnull null.1).elim
      · subst src
        by_cases mismatch : s₁.mode = DICT ∧
            (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off len.toNat)).toUInt64 ≠ s₁.check
        · have actual := Zlib.Inflate.Proofs.inflateSetDictionary_dataerr_any good₁.live get room mismatch.1 mismatch.2
          cases Except.ok.inj (hrun.symm.trans actual)
          exact fun _ => Or.inl
        · have checked : s₁.mode = DICT →
              (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off len.toNat)).toUInt64 = s₁.check := by
            intro dict
            exact Classical.byContradiction fun wrong => mismatch ⟨dict, wrong⟩
          have unowned := Zlib.Inflate.Proofs.callerRange_private_window good₁ args rfl
          obtain ⟨wr, heap1, state1, windowRun, good1, _, _, _, outcome⟩ :=
            Zlib.Inflate.Proofs.updatewindow_decoder_boundary good₁ inv₁.alloc.1 get (by omega : len.toNat ≤ off + len.toNat) room unowned
          have actual := Zlib.Inflate.Proofs.inflateSetDictionary_window_cut good₁.live get room allowed checked windowRun good1.live.hs
          have kw := Zlib.Inflate.KeepProofs.keep_updatewindow (some r₁) (.ref ref (off + len.toNat)) len h wr heap1 windowRun
          obtain ⟨s₀, hs₀, ctl⟩ := kw.states zs state1 good1.live.hs
          have es₀ : s₀ = s₁ := Option.some.inj (hs₀.symm.trans good₁.live.hs)
          subst s₀
          rcases outcome with success | ⟨failure, _, sameState, _⟩
          · subst wr
            simp only [ite_true] at actual
            have heapEq := congrArg Prod.snd (Except.ok.inj (hrun.symm.trans actual))
            dsimp only at heapEq
            have stateEq : state = { state1 with havedict := 1 } := by
              apply Option.some.inj
              rw [← next.good.live.hs, heapEq]
              simp [Zlib.Inflate.Spec.setI]
            intro b hown
            rw [inflate_owned_eq next.good b] at hown
            rcases hown with rfl | hwin
            · left; rw [inflate_owned_eq good₁]; exact Or.inl rfl
            · rw [stateEq] at hwin
              rcases ctl.fresh with hsame | ⟨w, hw, hnb⟩
              · left; rw [inflate_owned_eq good₁]; right; rw [← hsame]; exact hwin
              · rw [hw] at hwin; cases hwin
                right; exact good₁.fresh b hnb
          · subst wr
            rw [sameState] at actual
            simp only [show ¬ ((1 : Int32) = 0) from by decide, ite_false] at actual
            have heapEq := congrArg Prod.snd (Except.ok.inj (hrun.symm.trans actual))
            dsimp only at heapEq
            have stateEq : state = { s₁ with mode := MEM } := by
              apply Option.some.inj
              rw [← next.good.live.hs, heapEq]
              simp [Zlib.Inflate.Spec.setI]
            intro b hown
            rw [inflate_owned_eq next.good b, stateEq] at hown
            left; rw [inflate_owned_eq good₁ b]; exact hown
  | inflateGetHeader p head =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    have hrun : C.run (Zlib.Inflate.inflateGetHeader (some r₁) head) h = .ok (val, after) :=
      Zlib.Inflate.Proofs.run_of_heapCall run
    obtain ⟨memory, present⟩ := args
    by_cases nogzip : s₁.wrap &&& 2 = 0
    · cases Except.ok.inj (hrun.symm.trans (Zlib.Inflate.Proofs.inflateGetHeader_nogzip good₁.live head nogzip))
      exact fun _ => Or.inl
    · rcases memory with none | ⟨gb, gh, pointer, get, _⟩
      · exact absurd none present
      · subst pointer
        obtain ⟨h', run', _, good', _, _⟩ := Zlib.Inflate.Proofs.inflateGetHeader_ok good₁ (g := .tab gb) get nogzip
        cases Except.ok.inj (hrun.symm.trans run')
        intro b hown
        rw [inflate_owned_eq good' b] at hown
        left; rw [inflate_owned_eq good₁ b]; exact hown
  | inflateSync p =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    have hrun : C.run (Zlib.Inflate.inflateSync (some r₁)) h = .ok (val, after) :=
      Zlib.Inflate.Proofs.run_of_heapCall run
    obtain ⟨rc, after', stream, state, wb, run', good', _, window⟩ :=
      Zlib.Inflate.Proofs.inflateSync_total inv₁ args
    cases Except.ok.inj (hrun.symm.trans run')
    intro b hown
    rw [inflate_owned_eq good' b] at hown
    left; rw [inflate_owned_eq good₁ b]
    rcases hown with rfl | hwin
    · exact Or.inl rfl
    · right; rw [window] at hwin
      split at hwin
      · cases hwin
      · exact hwin
  | inflateSyncPoint p =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    have hrun : C.run (Zlib.Inflate.inflateSyncPoint (some r₁)) h = .ok (val, after) :=
      Zlib.Inflate.Proofs.run_of_heapCall run
    cases Except.ok.inj (hrun.symm.trans (Zlib.Inflate.Proofs.inflateSyncPoint_spec good₁.live))
    exact fun _ => Or.inl
  | inflateMark p =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    have hrun : C.run (Zlib.Inflate.inflateMark (some r₁)) h = .ok (val, after) :=
      Zlib.Inflate.Proofs.run_of_heapCall run
    obtain ⟨v, run', _⟩ := Zlib.Inflate.Proofs.inflateMark_spec good₁.live
    cases Except.ok.inj (hrun.symm.trans run')
    exact fun _ => Or.inl
  | inflateCodesUsed p =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    have hrun : C.run (Zlib.Inflate.inflateCodesUsed (some r₁)) h = .ok (val, after) :=
      Zlib.Inflate.Proofs.run_of_heapCall run
    obtain ⟨_, _, _, run'⟩ := Zlib.Inflate.Proofs.inflateCodesUsed_spec good₁
    cases Except.ok.inj (hrun.symm.trans run')
    exact fun _ => Or.inl
  | inflateValidate p check =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    have hrun : C.run (Zlib.Inflate.inflateValidate (some r₁) check) h = .ok (val, after) :=
      Zlib.Inflate.Proofs.run_of_heapCall run
    obtain ⟨h', run', _, good', _⟩ := Zlib.Inflate.Proofs.inflateValidate_safe good₁ check
    cases Except.ok.inj (hrun.symm.trans run')
    intro b hown
    rw [inflate_owned_eq good' b] at hown
    left; rw [inflate_owned_eq good₁ b]; exact hown
  | inflateUndermine p subvert =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    have hrun : C.run (Zlib.Inflate.inflateUndermine (some r₁) subvert) h = .ok (val, after) :=
      Zlib.Inflate.Proofs.run_of_heapCall run
    obtain ⟨h', run', _, good'⟩ := Zlib.Inflate.Proofs.inflateUndermine_safe good₁ subvert
    cases Except.ok.inj (hrun.symm.trans run')
    intro b hown
    rw [inflate_owned_eq good' b] at hown
    left; rw [inflate_owned_eq good₁ b]; exact hown
  | _ => simp [StreamOperation] at op

private theorem deflate_owned_of_step {h after : Heap} {r : ZStreamRef} {ds : Nat}
    {z z' : ZStream} {d d' : DeflateState}
    (good : Zlib.Deflate.Spec.DGood h r ds z d)
    (good' : Zlib.Deflate.Spec.DGood after r ds z' d')
    (same : ∀ b, DeflateOwned ds d' b → DeflateOwned ds d b) :
    ∀ b, StreamOwned after r b → StreamOwned h r b := by
  intro b hown
  rw [Zlib.Deflate.Engine.Proofs.stream_owned_deflate good' b] at hown
  rw [Zlib.Deflate.Engine.Proofs.stream_owned_deflate good b]
  exact same b hown

private theorem deflate_op_owned_within
    {h after : Heap} {r₁ : ZStreamRef} {ds : Nat} {z₁ : ZStream} {d₁ : DeflateState}
    {call : Call} {val : call.Result}
    (inv₁ : Zlib.Deflate.Universal.DInv h r₁ ds z₁ d₁)
    (hdr₁ : Zlib.Deflate.Universal.HeaderInv d₁)
    (calls₁ : Zlib.Deflate.Universal.CallFacts d₁)
    (op : StreamOperation .deflate r₁ call)
    (args : StreamArguments h r₁ call)
    (run : call.execute default h = .ok ((val, default), after)) :
    ∀ b, StreamOwned after r₁ b → StreamOwned h r₁ b := by
  have good₁ := inv₁.good
  have facts := Zlib.Deflate.Universal.sequence_facts
  cases call with
  | deflate p flush =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    obtain ⟨rc, after', z', d', used, out, run', inv', _, blocks⟩ :=
      facts.deflateCall inv₁ hdr₁ calls₁ args.1 args.2 flush
    have runE : Call.execute (.deflate (some r₁) flush) default h = .ok ((rc, default), after') :=
      Zlib.Deflate.Universal.heapCall_run run'
    have eq := Except.ok.inj (run.symm.trans runE)
    obtain ⟨-, rfl⟩ := eq
    exact deflate_owned_of_step good₁ inv'.good (fun b hb => (blocks b).mpr hb)
  | deflateReset p =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    obtain ⟨d0, tb, tbuf, hB, -⟩ := good₁.trees
    have e0 : d0 = d₁ := Option.some.inj (hB.dstate.symm.trans good₁.live.hs)
    rw [e0] at hB
    obtain ⟨a1, a2, a3, eK, -, -, -, _, _⟩ :=
      Zlib.Deflate.Proofs.GeneralInit.resetKeep_initial good₁.live hB good₁.inv.wrap_lo good₁.inv.wrap_hi
    obtain ⟨c1, c2, c3, h1, e1, rfl, -, -, -, goodA, _⟩ :=
      Zlib.Deflate.Proofs.deflateResetKeep_safe good₁
    have same := eK.symm.trans e1
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at same
    have states := congrArg (fun g : Heap => g.dstates ds) same
    simp only [Zlib.Deflate.Proofs.setD_dstates_same, Option.some.injEq] at states
    have l1 : a1 = c1 := congrArg DeflateState.dyn_ltree states
    have l2 : a2 = c2 := congrArg DeflateState.dyn_dtree states
    have l3 : a3 = c3 := congrArg DeflateState.bl_tree states
    subst l1 l2 l3
    obtain ⟨q, qa, h2, e2, hq, _, _, good2, _⟩ := Zlib.Deflate.Proofs.lm_init_safe goodA
    have run' : C.run (Zlib.Deflate.deflateReset (some r₁)) h = .ok (Z_OK, h2) := by
      have hz1 := goodA.live
      unfold Zlib.Deflate.deflateReset
      rw [C.run] at e1 ⊢
      simp only [bind_app, e1, beq_self_eq_true, ↓reduceIte, Zlib.Deflate.Proofs.zrd_eq,
        hz1.hz, hz1.zst, Zlib.Deflate.Proofs.castD, pure_app]
      rw [C.run] at e2; rw [e2]
    have eq := Except.ok.inj (run.symm.trans (Zlib.Deflate.Universal.heapCall_run run'))
    obtain ⟨-, rfl⟩ := eq
    exact deflate_owned_of_step good₁ good2 (fun b hb => by
      simpa [DeflateOwned, Zlib.Deflate.Spec.rkPost, Zlib.Deflate.Spec.rkPost3,
        Zlib.Deflate.Spec.rkMid, Zlib.Deflate.Spec.lmD, Zlib.Trees.Proofs.Out.ibRec,
        Zlib.Trees.Proofs.Out.trInitRec] using hb)
  | deflateParams p level strategy =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    by_cases refuse : (decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) < 0) ||
        decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) > 9) ||
        decide (strategy < 0) || decide (strategy > Z_FIXED)) = true
    · have run' : Call.execute (.deflateParams (some r₁) level strategy) default h =
          .ok ((Z_STREAM_ERROR, default), h) := by
        simp only [Call.execute, heapCall]
        rw [Zlib.Deflate.Universal.params_source]
        simp only [bind_app, Zlib.Deflate.Proofs.stateCheck_live good₁.live, bne_self_eq_false,
          Bool.false_eq_true, ite_false, Zlib.Deflate.Proofs.zrd_eq, good₁.live.hz, good₁.live.zst,
          Zlib.Deflate.Proofs.castD, refuse, ite_true, pure_app]
      obtain ⟨-, rfl⟩ := Except.ok.inj (run.symm.trans run')
      exact fun _ => id
    have rangeB : (decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) < 0) ||
        decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) > 9) ||
        decide (strategy < 0) || decide (strategy > Z_FIXED)) = false := by simpa using refuse
    have ranges : 0 ≤ (if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt ∧
        (if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt ≤ 9 ∧
        0 ≤ strategy.toInt ∧ strategy.toInt ≤ 4 := by
      have r2 := rangeB
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Int32.lt_iff_toInt_lt, GT.gt] at r2
      obtain ⟨⟨⟨a, b⟩, c⟩, e⟩ := r2
      have z0 : (0 : Int32).toInt = 0 := rfl
      have n9 : (9 : Int32).toInt = 9 := rfl
      have f4 : Z_FIXED.toInt = 4 := rfl
      omega
    obtain ⟨lo, hi, slo, shi⟩ := ranges
    by_cases same : strategy = d₁.strategy ∧
        (Zlib.Deflate.configuration_table[d₁.level.toInt.toNat]!).func =
          (Zlib.Deflate.configuration_table[(if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt.toNat]!).func
    · obtain ⟨lv, lvDef⟩ : ∃ x, x = if level == Z_DEFAULT_COMPRESSION then 6 else level := ⟨_, rfl⟩
      rw [← lvDef] at lo hi same rangeB
      have stateRun : Zlib.Deflate.zrd (some r₁) (·.state) h = .ok (z₁.state, h) := by
        rw [Zlib.Deflate.Proofs.zrd_eq, good₁.live.hz]
      have ldRun : ldDeflateState (some (.tab ds)) h = .ok (d₁, h) :=
        ldDeflateState_tab good₁.live.hs
      have cfgD := Zlib.Deflate.Proofs.config_at_run h good₁.inv.level_lo good₁.inv.level_hi
      have cfgL := Zlib.Deflate.Proofs.config_at_run h lo hi
      have stratB : (strategy != d₁.strategy) = false := by simp [same.1]
      have funcB : ((Zlib.Deflate.configuration_table[d₁.level.toInt.toNat]!).func !=
          (Zlib.Deflate.configuration_table[lv.toInt.toNat]!).func) = false := by
        rw [same.2]; exact bne_self_eq_false _
      have toTail : ∀ out, Zlib.Deflate.Universal.paramsTail (some (.tab ds)) lv strategy h = out →
          Call.execute (.deflateParams (some r₁) level strategy) default h =
            (out.map fun p => ((p.1, default), p.2)) := by
        intro out tail
        simp only [Call.execute, heapCall]
        rw [Zlib.Deflate.Universal.params_source, ← lvDef]
        simp only [bind_app, Zlib.Deflate.Proofs.stateCheck_live good₁.live, bne_self_eq_false,
          Bool.false_eq_true, ite_false, stateRun, good₁.live.zst, Zlib.Deflate.Proofs.castD,
          rangeB, ldRun, cfgD, stratB, cfgL, funcB, pure_app, Bool.false_and, tail]
        rcases out with e | ⟨v, a⟩ <;> rfl
      by_cases sameLevel : d₁.level = lv
      · have levelB : (d₁.level != lv) = false := by simp [sameLevel]
        have stateEq : ({ d₁ with strategy := strategy } : DeflateState) = d₁ := by rw [same.1]
        have tailRun : Zlib.Deflate.Universal.paramsTail (some (.tab ds)) lv strategy h = .ok (Z_OK, h) := by
          unfold Zlib.Deflate.Universal.paramsTail
          simp only [bind_app, ldRun, levelB, Bool.false_eq_true, ite_false,
            Zlib.Deflate.Proofs.wrD_eq, good₁.live.hs, stateEq, Zlib.Deflate.Proofs.setD_self good₁.live.hs]
          rfl
        obtain ⟨-, rfl⟩ := Except.ok.inj (run.symm.trans (toTail _ tailRun))
        exact fun _ => id
      · have hdl1 := good₁.inv.level_lo
        have hdl2 := good₁.inv.level_hi
        have cls := Zlib.Deflate.Universal.func_class (a := d₁.level.toInt.toNat) (b := lv.toInt.toNat)
          (by omega) (by omega) same.2
        have dNonzero : d₁.level ≠ 0 := by
          intro zero; apply sameLevel
          rw [zero]; have : lv.toInt.toNat = 0 := cls.1.mp (by rw [zero]; rfl)
          apply Int32.toInt_inj.mp; change (0 : Int) = lv.toInt; omega
        have levelB : (d₁.level != lv) = true := by simpa using sameLevel
        have zeroB : (d₁.level == 0 && d₁.«matches» != 0) = false := by simp [dNonzero]
        let c := Zlib.Deflate.configuration_table[lv.toInt.toNat]!
        let d2 := Zlib.Deflate.Universal.paramsState d₁ lv strategy c
        have tailRun : Zlib.Deflate.Universal.paramsTail (some (.tab ds)) lv strategy h =
            .ok (Z_OK, Zlib.Deflate.Spec.setD h ds d2) := by
          unfold Zlib.Deflate.Universal.paramsTail
          simp only [bind_app, ldRun, levelB, ite_true, zeroB, Bool.false_eq_true, ite_false, cfgL,
            Zlib.Deflate.Proofs.wrD_eq, good₁.live.hs, Zlib.Deflate.Proofs.setD_dstates_same,
            Zlib.Deflate.Proofs.setD_setD]
          rfl
        have inv2 : Zlib.Deflate.Spec.DStInv h ds d2 :=
          { good₁.inv with
            blocks := good₁.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            level_lo := lo, level_hi := hi, strat_lo := slo, strat_hi := shi }
        have good2 : Zlib.Deflate.Spec.DGood (Zlib.Deflate.Spec.setD h ds d2) r₁ ds z₁ d2 :=
          good₁.setD' rfl good₁.live.status inv2 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        obtain ⟨-, rfl⟩ := Except.ok.inj (run.symm.trans (toTail _ tailRun))
        exact deflate_owned_of_step good₁ good2 (fun b hb => by
          simpa [DeflateOwned, d2, Zlib.Deflate.Universal.paramsState] using hb)
    · have differs : strategy ≠ d₁.strategy ∨
          (Zlib.Deflate.configuration_table[d₁.level.toInt.toNat]!).func ≠
            (Zlib.Deflate.configuration_table[(if level == Z_DEFAULT_COMPRESSION then 6 else level).toInt.toNat]!).func := by
        by_cases s : strategy = d₁.strategy
        · exact Or.inr (fun f => same ⟨s, f⟩)
        · exact Or.inl s
      have source := Zlib.Deflate.Universal.params_differs good₁ level strategy rangeB lo hi differs
      by_cases reset : d₁.last_flush = -2
      · have resetB : (d₁.last_flush != -2) = false := by simp [reset]
        obtain ⟨after', dF, tailRun, invF, _, _, _, _, _, _, ownedF, _, _, _, _⟩ :=
          Zlib.Deflate.Universal.params_tail inv₁ (Zlib.Deflate.Universal.Flushed.of_reset calls₁ reset) _ strategy lo hi slo shi
        have run' : Zlib.Deflate.deflateParams (some r₁) level strategy h = .ok (Z_OK, after') := by
          rw [source, resetB]; exact tailRun
        obtain ⟨-, rfl⟩ := Except.ok.inj (run.symm.trans (Zlib.Deflate.Universal.heapCall_run run'))
        exact deflate_owned_of_step good₁ invF.good (fun b hb => (ownedF b).mp hb)
      · have resetB : (d₁.last_flush != -2) = true := by simpa using reset
        obtain ⟨rc, after1, zA, dA, used, out, run1, inv1, _, owned1⟩ :=
          facts.deflateCall inv₁ hdr₁ calls₁ args.1 args.2 Z_BLOCK
        have flushRun : ∀ v a, Zlib.Deflate.Universal.paramsAfter (some r₁) (some (.tab ds))
            (if level == Z_DEFAULT_COMPRESSION then 6 else level) strategy rc after1 = .ok (v, a) →
            Zlib.Deflate.deflateParams (some r₁) level strategy h = .ok (v, a) := by
          intro v a e
          rw [source, ite_eq_left resetB, Zlib.Deflate.Universal.params_flush_split]
          simp only [bind_app, show Zlib.Deflate.deflate (some r₁) Z_BLOCK h = .ok (rc, after1) from run1]
          exact e
        rcases Zlib.Deflate.Universal.params_after_outcome inv1 rc _ strategy lo hi slo shi with
          ⟨v, stop⟩ | ⟨after', dF, tailRun, invF, _, _, _, _, _, _, ownedF, _, _, _, _⟩
        · obtain ⟨-, rfl⟩ := Except.ok.inj (run.symm.trans (Zlib.Deflate.Universal.heapCall_run (flushRun v after1 stop)))
          exact deflate_owned_of_step good₁ inv1.good (fun b hb => (owned1 b).mpr hb)
        · obtain ⟨-, rfl⟩ := Except.ok.inj (run.symm.trans (Zlib.Deflate.Universal.heapCall_run (flushRun Z_OK after' tailRun)))
          exact deflate_owned_of_step good₁ invF.good (fun b hb => (owned1 b).mpr ((ownedF b).mp hb))
  | deflatePrime p bits value =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    by_cases range : bits.toInt < 0 ∨ 16 < bits.toInt
    · have run' := Zlib.Deflate.Proofs.deflatePrime_invalid_count good₁.live bits value range
      obtain ⟨-, rfl⟩ := Except.ok.inj (run.symm.trans (Zlib.Deflate.Universal.heapCall_run run'))
      exact fun _ => id
    · have b0 : 0 ≤ bits.toInt := by omega
      have b16 : bits.toInt ≤ 16 := by omega
      have symZero : d₁.sym_next = 0 := by
        obtain ⟨z', i, s, get, zst, hs', st⟩ := args
        have zz : z' = z₁ := Option.some.inj (get.symm.trans good₁.live.hz)
        subst zz; rw [good₁.live.zst] at zst; cases zst
        have ss : s = d₁ := Option.some.inj (hs'.symm.trans good₁.live.hs)
        subst ss
        exact hdr₁.empty (st.elim Or.inl (fun g => Or.inr (Or.inl g)))
      obtain ⟨d0, b, buf, trees⟩ := good₁.trees
      have e0 : d0 = d₁ := Option.some.inj (trees.base.dstate.symm.trans good₁.live.hs)
      rw [e0] at trees
      obtain ⟨w, p', q, b', blocks⟩ := good₁.inv.blocks
      have bb : b = b' := by
        have e := blocks.pbuf
        rw [trees.base.pbuf] at e; cases e; rfl
      subst bb
      obtain ⟨off, pout, offFit⟩ := blocks.pout
      have v0 : 0 ≤ d₁.bi_valid.toInt := good₁.inv.bits.1
      have v7 : d₁.bi_valid.toInt ≤ 7 := inv₁.shape.biValid
      have notRange : (bits < 0 || bits > 16) = false := by
        have l1 : ¬ bits < 0 := fun lt => by have := Int32.lt_iff_toInt_lt.mp lt; simp at this; omega
        have l2 : ¬ bits > 16 := fun lt => by have := Int32.lt_iff_toInt_lt.mp lt; simp at this; omega
        simp [l1, l2]
      have move : ∃ (a : Array UInt8), Zlib.Deflate.deflatePrime (some r₁) bits value h =
          Zlib.Deflate.Universal.primeTail (some (.tab ds)) bits value
            (Zlib.Deflate.Spec.setD (Zlib.Trees.Proofs.Out.setB h b a) ds { d₁ with pending_out := d₁.pending_buf }) ∧
          a.size = buf.size := by
        by_cases mv : d₁.pending_out = d₁.pending_buf
        · refine ⟨buf, ?_, rfl⟩
          have same : ({ d₁ with pending_out := d₁.pending_buf } : DeflateState) = d₁ := by
            cases d₁; simp only at mv; subst mv; rfl
          rw [same, Zlib.Deflate.Universal.self_heap trees.base.bytes good₁.live.hs, Zlib.Deflate.Universal.prime_split]
          simp [Zlib.Deflate.Proofs.stateCheck_live good₁.live, Zlib.Deflate.Proofs.zrd_eq,
            good₁.live.hz, good₁.live.zst, Zlib.Deflate.Proofs.castD, Zlib.Deflate.Proofs.ldD_eq,
            good₁.live.hs, notRange, mv]
        · have psz := trees.base.psize
          obtain ⟨st, a, loop, size⟩ := Zlib.Deflate.Universal.move_loop trees.base.bytes trees.base.rw d₁.pending (off := off)
            (by omega)
          have loop' : C.cwhile Zlib.Deflate.Universal.moveCond Zlib.Deflate.Universal.moveBody
              (d₁.pending, d₁.pending_buf, d₁.pending_out) h = .ok (st, Zlib.Trees.Proofs.Out.setB h b a) := by
            rw [trees.base.pbuf, pout]; exact loop
          refine ⟨a, ?_, size⟩
          rw [Zlib.Deflate.Universal.prime_split]
          simp [Zlib.Deflate.Proofs.stateCheck_live good₁.live, Zlib.Deflate.Proofs.zrd_eq,
            good₁.live.hz, good₁.live.zst, Zlib.Deflate.Proofs.castD, Zlib.Deflate.Proofs.ldD_eq,
            good₁.live.hs, notRange, mv, loop', Zlib.Deflate.Proofs.wrD_eq]
      obtain ⟨a, runMove, sizeA⟩ := move
      obtain ⟨good1, trees1⟩ := Zlib.Deflate.Universal.move_good good₁ trees sizeA
      obtain ⟨rc, bf, e, runTail, _, size2, ⟨p2, w2, v2, u2, rfl⟩, _⟩ :=
        Zlib.Deflate.Universal.prime_tail bits value trees1 b0 b16 v0 v7
      have heapEq : Zlib.Deflate.Spec.setD
          (Zlib.Trees.Proofs.Out.setB
            (Zlib.Deflate.Spec.setD (Zlib.Trees.Proofs.Out.setB h b a) ds { d₁ with pending_out := d₁.pending_buf })
            b bf) ds
          { d₁ with pending_out := d₁.pending_buf, pending := p2, bi_buf := w2, bi_valid := v2, bi_used := u2 } =
          Zlib.Deflate.Spec.setD (Zlib.Trees.Proofs.Out.setB h b bf) ds
          { d₁ with pending_out := d₁.pending_buf, pending := p2, bi_buf := w2, bi_valid := v2, bi_used := u2 } :=
        Zlib.Deflate.Universal.setD_setB_twice h b ds a bf _ _
      rw [heapEq] at runTail
      have eq := Except.ok.inj (run.symm.trans (Zlib.Deflate.Universal.heapCall_run (runMove.trans runTail)))
      obtain ⟨-, rfl⟩ := eq
      intro x hx
      rcases hx with ⟨z', get', hcase⟩
      have getSet : r₁.get (Zlib.Deflate.Spec.setD (Zlib.Trees.Proofs.Out.setB h b bf) ds
          { d₁ with pending_out := d₁.pending_buf, pending := p2, bi_buf := w2, bi_valid := v2, bi_used := u2 }) = r₁.get h := by
        cases r₁ <;> rfl
      rw [getSet] at get'
      have ez : z' = z₁ := Option.some.inj (get'.symm.trans good₁.live.hz)
      subst z'
      refine ⟨z₁, good₁.live.hz, ?_⟩
      rcases hcase with ⟨i', s', zst, _, _⟩ | ⟨i', d', zst, hd', hdo⟩
      · rw [good₁.live.zst] at zst; cases zst
      · rw [good₁.live.zst] at zst; cases zst
        simp only [Zlib.Deflate.Spec.setD, Zlib.Trees.Proofs.Out.setB, upd_same, Option.some.injEq] at hd'
        subst hd'
        right; refine ⟨ds, d₁, good₁.live.zst, good₁.live.hs, ?_⟩
        simpa [DeflateOwned] using hdo
  | deflateGetDictionary p dict hasLen =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    obtain ⟨z', i, s, get, zst, hs, range⟩ := args
    have zz : z' = z₁ := Option.some.inj (get.symm.trans good₁.live.hz)
    subst zz; rw [good₁.live.zst] at zst; cases zst
    have ss : s = d₁ := Option.some.inj (hs.symm.trans good₁.live.hs)
    subst ss
    obtain ⟨after', run', inv', hget', hd', _, _⟩ :=
      Zlib.Deflate.Universal.getDictionary_view inv₁ dict hasLen range (fun _ => False)
    obtain ⟨-, rfl⟩ := Except.ok.inj (run.symm.trans (Zlib.Deflate.Universal.heapCall_run run'))
    exact deflate_owned_of_step good₁ inv'.good (fun _ => id)
  | deflateSetDictionary p dict len =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    rcases Zlib.Deflate.Universal.setdict_cases inv₁ dict len with refused | ⟨null, la0, pass, body⟩
    · obtain ⟨-, rfl⟩ := Except.ok.inj (run.symm.trans (Zlib.Deflate.Universal.heapCall_run refused))
      exact fun _ => id
    · obtain ⟨after', zF, dF, bodyRun, invF, _, _, _, _, ownedF, _, _⟩ :=
        Zlib.Deflate.Universal.setdict_body_all inv₁ dict len args null la0
          (Zlib.Deflate.Universal.setdict_sym0 inv₁.shape inv₁.good.inv.wrap_lo inv₁.good.inv.wrap_hi
            hdr₁ (calls₁.finishSym) pass)
      obtain ⟨-, rfl⟩ := Except.ok.inj (run.symm.trans (Zlib.Deflate.Universal.heapCall_run (body.trans bodyRun)))
      exact deflate_owned_of_step good₁ invF.good (fun b hb => (ownedF b).mp hb)
  | deflateSetHeader p head =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    by_cases wrap : d₁.wrap = 2
    · obtain ⟨after', run', _, good', _⟩ :=
        Zlib.Deflate.Proofs.deflateSetHeader_safe good₁ wrap head (Zlib.Deflate.Universal.gzOk_any h head)
      obtain ⟨-, rfl⟩ := Except.ok.inj (run.symm.trans (Zlib.Deflate.Universal.heapCall_run run'))
      exact deflate_owned_of_step good₁ good' (fun b hb => by
        simpa [DeflateOwned, Zlib.Deflate.Spec.setHeaderD] using hb)
    · have run' : C.run (Zlib.Deflate.deflateSetHeader (some r₁) head) h = .ok (Z_STREAM_ERROR, h) := by
        unfold C.run Zlib.Deflate.deflateSetHeader
        simp [Zlib.Deflate.Proofs.stateCheck_live good₁.live, Zlib.Deflate.Proofs.zrd_eq,
          good₁.live.hz, good₁.live.zst, Zlib.Deflate.Proofs.castD, Zlib.Deflate.Proofs.rdD_eq,
          good₁.live.hs, wrap]
      obtain ⟨-, rfl⟩ := Except.ok.inj (run.symm.trans (Zlib.Deflate.Universal.heapCall_run run'))
      exact fun _ => id
  | deflateTune p g m n c =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    obtain ⟨after', run', _, good', _⟩ := Zlib.Deflate.Proofs.deflateTune_safe good₁ g m n c
    obtain ⟨-, rfl⟩ := Except.ok.inj (run.symm.trans (Zlib.Deflate.Universal.heapCall_run run'))
    exact deflate_owned_of_step good₁ good' (fun b hb => by
      simpa [DeflateOwned, Zlib.Deflate.Spec.tuneD] using hb)
  | deflatePending p hp hb =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    have run' := Zlib.Deflate.Proofs.deflatePending_run good₁.live hp hb
    obtain ⟨-, rfl⟩ := Except.ok.inj (run.symm.trans (Zlib.Deflate.Universal.heapCall_run run'))
    exact fun _ => id
  | deflateUsed p hb =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    have run' := Zlib.Deflate.Proofs.deflateUsed_run good₁.live hb
    obtain ⟨-, rfl⟩ := Except.ok.inj (run.symm.trans (Zlib.Deflate.Universal.heapCall_run run'))
    exact fun _ => id
  | deflateBound p n =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    obtain ⟨_, _, run'⟩ := Zlib.Deflate.Proofs.deflateBound_safe good₁
      (Zlib.Deflate.Universal.hdrStrOk_of_live inv₁ args.2) n
    obtain ⟨-, rfl⟩ := Except.ok.inj (run.symm.trans (Zlib.Deflate.Universal.heapCall_run run'))
    exact fun _ => id
  | deflateBound_z p n =>
    simp [StreamOperation] at op; obtain ⟨_, rfl⟩ := op
    obtain ⟨_, _, run'⟩ := Zlib.Deflate.Proofs.deflateBound_z_safe good₁
      (Zlib.Deflate.Universal.hdrStrOk_of_live inv₁ args.2) n
    obtain ⟨-, rfl⟩ := Except.ok.inj (run.symm.trans (Zlib.Deflate.Universal.heapCall_run run'))
    exact fun _ => id
  | _ => simp [StreamOperation] at op

/-- `Goal.multi_stream_init_disjoint` -/
theorem multi_stream_init_disjoint : Goal.multi_stream_init_disjoint := by
  refine ⟨?_, ?_⟩
  · intro h after r₁ r₂ z₂ kind₁ version wb reach₁ hg hne hz₂ hd₂ hv run hfit
    have inv₁ := streamInvariant_of_reach reach₁
    obtain ⟨hf, hu, ⟨z₁, hz₁⟩⟩ := streamInvariant_facts inv₁
    have reach₂ : StreamReachable .inflate after r₂ :=
      StreamReachable.inflateInit hf hu hg hz₂ hd₂ hv run
    obtain ⟨rc', after', run', hnalloc, hbr⟩ :=
      (ZlibF.Spec.Public.Proofs.InflateInit.inflate_init2_public wb).2.2 h r₂ z₂ version hf hu hg hz₂ hd₂ hv
    have eq := Except.ok.inj (run.symm.trans run')
    obtain ⟨hrc, ha_eq⟩ := Prod.mk.inj eq
    subst after'
    by_cases ha : h.allocOk h.nalloc = false
    · rw [ite_eq_left ha] at hbr
      rw [← hrc] at hbr
      have hc : Z_OK = Z_MEM_ERROR := hbr.1
      cases hc
    · rw [ite_eq_right ha] at hbr
      cases hw : Api.inflWbits wb.toInt with
      | none =>
        rw [hw] at hbr
        rw [← hrc] at hbr
        have hc : Z_OK = Z_STREAM_ERROR := hbr.1
        cases hc
      | some p =>
        obtain ⟨wrap, bits⟩ := p
        rw [hw] at hbr
        obtain ⟨z', s', hgood', _, _, _, hwin, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hfr, hlc⟩ := hbr.2
        have hbframe : BufferFrame h after (StreamRoot r₂) [] := ⟨hfr, fun _ hm => by cases hm⟩
        have noRoot : ∀ b, StreamRoot r₁ b → ¬ StreamRoot r₂ b :=
          uniq_streamRoot_disjoint hu hne hz₁ hz₂
        have noOwn : ∀ b, StreamOwned h r₁ b → ¬ StreamRoot r₂ b :=
          fun b hown hr2 => uniq_streamRoot_not_streamOwned inv₁ hu hz₂ b hr2 hown
        have noExt : ∀ reg ∈ ([] : List Region), ∀ b, ByteRoot reg.pointer b → ¬ StreamOwned h r₁ b :=
          fun _ hm => by cases hm
        have hgAfter : LibraryGlobals after := by
          unfold LibraryGlobals at hg ⊢; rw [← hfr.1]; exact hg
        obtain ⟨_, _, hown₁, hrest₁⟩ := rebuffer_of_step_frame reach₁ inv₁ hgood'.fresh hgood'.uniq hgAfter
          hbframe noRoot noOwn noExt
        obtain ⟨reach₁', _⟩ := hrest₁ hfit
        have hdisj : StreamDisjoint after r₁ r₂ := by
          refine ⟨hne, fun b hown1 hown2 => ?_⟩
          have hown1_h : StreamOwned h r₁ b := (hown₁ b).mp hown1
          have hlive_b : h.live b := streamOwned_live inv₁ hown1_h
          rw [inflate_owned_eq hgood' b, hwin] at hown2
          rcases hown2 with rfl | hnull
          · exact hf h.nextBlk (Nat.le_refl _) hlive_b
          · cases hnull
        exact ⟨reach₁', reach₂, hdisj, hown₁⟩
  · intro h after r₁ r₂ z₂ kind₁ version level method wb mem strategy reach₁ hg hne hz₂ hd₂ hv run hfit
    have inv₁ := streamInvariant_of_reach reach₁
    obtain ⟨hf, hu, ⟨z₁, hz₁⟩⟩ := streamInvariant_facts inv₁
    have huD : Zlib.Deflate.Spec.Uniq h := hu
    have reach₂ : StreamReachable .deflate after r₂ :=
      StreamReachable.deflateInit hf huD hg hz₂ hd₂ hv run
    obtain ⟨rc', after', run', hbr⟩ :=
      (ZlibF.Spec.Public.Proofs.DeflateInit2.deflateInit2_proof level method wb mem strategy).2.2
        h r₂ z₂ version hf huD hg hz₂ hd₂ hv
    have eq := Except.ok.inj (run.symm.trans run')
    obtain ⟨hrc, ha_eq⟩ := Prod.mk.inj eq
    subst after'
    cases hp : Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt with
    | none =>
      rw [hp] at hbr
      rw [← hrc] at hbr
      have hc : Z_OK = Z_STREAM_ERROR := hbr.1
      cases hc
    | some params =>
      rw [hp] at hbr
      dsimp only at hbr
      by_cases ha : h.allocOk h.nalloc = false
      · rw [ite_eq_left ha] at hbr
        rw [← hrc] at hbr
        have hc : Z_OK = Z_MEM_ERROR := hbr.1
        cases hc
      · rw [ite_eq_right ha] at hbr
        obtain ⟨_, hbr2⟩ := hbr
        by_cases hall : (List.range 5).all (fun j => h.allocOk (h.nalloc + j)) = true
        · rw [ite_eq_left hall] at hbr2
          obtain ⟨z', s', hgood', _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hfr, _, hbounds⟩ := hbr2.2
          have hbframe : BufferFrame h after (StreamRoot r₂) [] := ⟨hfr, fun _ hm => by cases hm⟩
          have noRoot : ∀ b, StreamRoot r₁ b → ¬ StreamRoot r₂ b :=
            uniq_streamRoot_disjoint hu hne hz₁ hz₂
          have noOwn : ∀ b, StreamOwned h r₁ b → ¬ StreamRoot r₂ b :=
            fun b hown hr2 => uniq_streamRoot_not_streamOwned inv₁ hu hz₂ b hr2 hown
          have noExt : ∀ reg ∈ ([] : List Region), ∀ b, ByteRoot reg.pointer b → ¬ StreamOwned h r₁ b :=
            fun _ hm => by cases hm
          have hgAfter : LibraryGlobals after := by
            unfold LibraryGlobals at hg ⊢; rw [← hfr.1]; exact hg
          have huAfter : Zlib.Inflate.Spec.Uniq after := hgood'.uniq
          obtain ⟨_, _, hown₁, hrest₁⟩ := rebuffer_of_step_frame reach₁ inv₁ hgood'.fresh huAfter hgAfter
            hbframe noRoot noOwn noExt
          obtain ⟨reach₁', _⟩ := hrest₁ hfit
          have hdisj : StreamDisjoint after r₁ r₂ := by
            refine ⟨hne, fun b hown1 hown2 => ?_⟩
            have hown1_h : StreamOwned h r₁ b := (hown₁ b).mp hown1
            have hlive_b : h.live b := streamOwned_live inv₁ hown1_h
            rw [Zlib.Deflate.Engine.Proofs.stream_owned_deflate hgood' b] at hown2
            have hb_range := (hbounds b).mp hown2
            exact hf b hb_range.1 hlive_b
          exact ⟨reach₁', reach₂, hdisj, hown₁⟩
        · rw [ite_eq_right hall] at hbr2
          rw [← hrc] at hbr2
          have hc : Z_OK = Z_MEM_ERROR := hbr2.1
          cases hc

/-- `Goal.multi_stream_step_safety` -/
theorem multi_stream_step_safety : Goal.multi_stream_step_safety := by
  intro h r₁ r₂ kind₁ kind₂ call reach₁ reach₂ hg hdisj hfit op args hext
  have inv₂ := streamInvariant_of_reach reach₂
  have inv₁ := streamInvariant_of_reach reach₁
  obtain ⟨_, hu, ⟨z₁, hz₁⟩⟩ := streamInvariant_facts inv₁
  obtain ⟨_, _, ⟨z₂, hz₂⟩⟩ := streamInvariant_facts inv₂
  have hstep1 : ∃ value after,
      call.execute default h = .ok ((value, default), after) ∧
      StreamInvariant kind₁ after r₁ ∧
      BufferFrame h after
        (fun b => StreamRoot r₁ b ∨ StreamOwned h r₁ b ∨ StreamHeaderRecord h r₁ call b)
        (StreamWriteRegions h r₁ call) ∧
      LiveChange h after
        (fun b => StreamOwned after r₁ b ∧ ¬ h.live b)
        (fun b => StreamOwned h r₁ b ∧ ¬ StreamOwned after r₁ b) ∧
      (∀ b, StreamOwned after r₁ b → StreamOwned h r₁ b ∨ ¬ h.live b) := by
    cases kind₁ with
    | inflate =>
      obtain ⟨value, after, run, inv₁', bframe, liveChange⟩ :=
        Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r₁ call reach₁ hfit op args
      obtain ⟨zs, z₁', s₁', invI, heldI⟩ := Zlib.Inflate.Proofs.reachable_invariant_kind reach₁ rfl
      exact ⟨value, after, run, inv₁', bframe, liveChange,
        inflate_op_owned_within invI heldI hfit op args run⟩
    | deflate =>
      obtain ⟨value, after, run, inv₁', bframe, liveChange⟩ :=
        Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r₁ call reach₁ hfit op args
      obtain ⟨ds, z₁', d₁', invD, hdrD, callsD⟩ :=
        Zlib.Deflate.Universal.reachable_inv_of Zlib.Deflate.Universal.sequence_facts reach₁
      exact ⟨value, after, run, inv₁', bframe, liveChange,
        fun b hb => Or.inl (deflate_op_owned_within invD hdrD callsD op args run b hb)⟩
  obtain ⟨value, after, run, inv₁', bframe, _, howned₁_within⟩ := hstep1
  have reach₁' : StreamReachable kind₁ after r₁ :=
    StreamReachable.step reach₁ (fun _ => hfit) op args run
  obtain ⟨freshAfter, uniqAfter, _⟩ := streamInvariant_facts inv₁'
  have hgAfter : LibraryGlobals after := by
    unfold LibraryGlobals at hg ⊢
    rw [← (restoreRegions_tables_other h after (StreamWriteRegions h r₁ call)).1]
    rw [← bframe.1.1]
    exact hg
  have noRoot : ∀ b, StreamRoot r₂ b →
      ¬ (StreamRoot r₁ b ∨ StreamOwned h r₁ b ∨ StreamHeaderRecord h r₁ call b) := by
    intro b hr2 hch
    rcases hch with hr1 | hown1 | hhdr
    · exact uniq_streamRoot_disjoint hu hdisj.1.symm hz₂ hz₁ b hr2 hr1
    · exact uniq_streamRoot_not_streamOwned inv₁ hu hz₂ b hr2 hown1
    · obtain ⟨g, hgz⟩ := streamHeaderRecord_gz op args hhdr
      exact (uniq_gzheader_not_other inv₂ hu hgz).1 hr2
  have noOwn : ∀ b, StreamOwned h r₂ b →
      ¬ (StreamRoot r₁ b ∨ StreamOwned h r₁ b ∨ StreamHeaderRecord h r₁ call b) := by
    intro b hown2 hch
    rcases hch with hr1 | hown1 | hhdr
    · exact uniq_streamRoot_not_streamOwned inv₂ hu hz₁ b hr1 hown2
    · exact hdisj.2 b hown1 hown2
    · obtain ⟨g, hgz⟩ := streamHeaderRecord_gz op args hhdr
      exact (uniq_gzheader_not_other inv₂ hu hgz).2 hown2
  have noExt : ∀ reg ∈ StreamWriteRegions h r₁ call, ∀ b, ByteRoot reg.pointer b → ¬ StreamOwned h r₂ b :=
    fun reg hreg b hbr => hext reg hreg b hbr
  obtain ⟨hreb₂, hz₂', hown₂, hrest₂⟩ :=
    rebuffer_of_step_frame reach₂ inv₂ freshAfter uniqAfter hgAfter bframe noRoot noOwn noExt
  obtain ⟨hr₂_eq, hframe₂⟩ := frame_of_restore_step inv₂ bframe noRoot noOwn noExt
  have hinv₂' : StreamInvariant kind₂ after r₂ :=
    streamInvariant_of_frame_other inv₂ hr₂_eq hframe₂ freshAfter uniqAfter
  have hdisj' : StreamDisjoint after r₁ r₂ := by
    refine ⟨hdisj.1, fun b hown1 hown2 => ?_⟩
    have hown2_h : StreamOwned h r₂ b := (hown₂ b).mp hown2
    rcases howned₁_within b hown1 with hown1_h | hdead
    · exact hdisj.2 b hown1_h hown2_h
    · exact hdead (streamOwned_live inv₂ hown2_h)
  exact ⟨value, after, run, inv₁', hinv₂', reach₁', fun hf => (hrest₂ hf).1,
    hreb₂, hz₂', hown₂, hdisj'⟩

/-- `Goal.multi_stream_end_safety` -/
theorem multi_stream_end_safety : Goal.multi_stream_end_safety := by
  intro h r₁ r₂ kind₁ kind₂ reach₁ reach₂ hg hdisj
  have inv₁ := streamInvariant_of_reach reach₁
  have inv₂ := streamInvariant_of_reach reach₂
  obtain ⟨_, hu, ⟨z₁, hz₁⟩⟩ := streamInvariant_facts inv₁
  obtain ⟨_, _, ⟨z₂, hz₂⟩⟩ := streamInvariant_facts inv₂
  have hend1 : ∃ rc after z₁',
      C.run ((match kind₁ with
        | .inflate => Zlib.Inflate.inflateEnd
        | .deflate => Zlib.Deflate.deflateEnd) (some r₁)) h = .ok (rc, after) ∧
      (rc = Z_OK ∨ kind₁ = .deflate ∧ rc = Z_DATA_ERROR) ∧
      r₁.get after = some z₁' ∧ z₁'.state = none ∧
      Frame h after (fun b => StreamRoot r₁ b ∨ StreamOwned h r₁ b) ∧
      LiveChange h after (fun _ => False) (StreamOwned h r₁) ∧
      Fresh after ∧ Zlib.Inflate.Spec.Uniq after := by
    cases kind₁ with
    | inflate =>
      obtain ⟨rc, after, z₁', run, hrc, hz₁', hstate, hfr, hlc⟩ :=
        Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.2 h r₁ reach₁
      dsimp [StreamInvariant] at inv₁
      obtain ⟨zs, z, s, good, dalloc⟩ := inv₁
      obtain ⟨h', run', _, hu', hf', _⟩ := Zlib.Inflate.Proofs.inflateEnd_safe good dalloc.2
      cases Except.ok.inj (run.symm.trans run')
      exact ⟨_, _, z₁', run, hrc, hz₁', hstate, hfr, hlc, hf', hu'⟩
    | deflate =>
      obtain ⟨rc, after, z₁', run, hrc, hz₁', hstate, hfr, hlc⟩ :=
        Zlib.Deflate.Universal.deflate_sequence_safety.2.2 h r₁ reach₁
      dsimp [StreamInvariant] at inv₁
      obtain ⟨ds, z, d, good, dalloc⟩ := inv₁
      obtain ⟨w, p, q, b, _, h', run', _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hu', hf', _⟩ :=
        Zlib.Deflate.Proofs.deflateEnd_safe good dalloc.2
      cases Except.ok.inj (run.symm.trans run')
      exact ⟨_, _, z₁', run, hrc, hz₁', hstate, hfr, hlc, hf', hu'⟩
  obtain ⟨rc, after, z₁', run, hrc, hz₁', hstate, hfr, hlc, hf', hu'⟩ := hend1
  have hbframe : BufferFrame h after (fun b => StreamRoot r₁ b ∨ StreamOwned h r₁ b) [] :=
    ⟨hfr, fun _ hm => by cases hm⟩
  have noRoot : ∀ b, StreamRoot r₂ b → ¬ (StreamRoot r₁ b ∨ StreamOwned h r₁ b) := by
    intro b hr2 hch
    rcases hch with hr1 | hown1
    · exact uniq_streamRoot_disjoint hu hdisj.1.symm hz₂ hz₁ b hr2 hr1
    · exact uniq_streamRoot_not_streamOwned inv₁ hu hz₂ b hr2 hown1
  have noOwn : ∀ b, StreamOwned h r₂ b → ¬ (StreamRoot r₁ b ∨ StreamOwned h r₁ b) := by
    intro b hown2 hch
    rcases hch with hr1 | hown1
    · exact uniq_streamRoot_not_streamOwned inv₂ hu hz₁ b hr1 hown2
    · exact hdisj.2 b hown1 hown2
  have noExt : ∀ reg ∈ ([] : List Region), ∀ b, ByteRoot reg.pointer b → ¬ StreamOwned h r₂ b :=
    fun _ hm => by cases hm
  have hgAfter : LibraryGlobals after := by
    unfold LibraryGlobals at hg ⊢; rw [← hfr.1]; exact hg
  obtain ⟨hreb₂, hz₂', hown₂, hrest₂⟩ :=
    rebuffer_of_step_frame reach₂ inv₂ hf' hu' hgAfter hbframe noRoot noOwn noExt
  obtain ⟨hr₂_eq, hframe₂⟩ := frame_of_restore_step inv₂ hbframe noRoot noOwn noExt
  have hinv₂' : StreamInvariant kind₂ after r₂ :=
    streamInvariant_of_frame_other inv₂ hr₂_eq hframe₂ hf' hu'
  exact ⟨rc, after, z₁', run, hrc, hz₁', hstate, hfr, hlc, hreb₂, hz₂', hown₂, hinv₂', fun hf => (hrest₂ hf).1⟩

private def nonvacHeapInit : Heap :=
  { witnessHeap with
    streams := upd witnessHeap.streams 3 (some default)
    nextBlk := 4 }

private theorem nonvac_fresh : Fresh nonvacHeapInit := by
  intro b hb
  dsimp [nonvacHeapInit] at hb
  have hne0 : b ≠ 0 := by omega
  have hne1 : b ≠ 1 := by omega
  have hne2 : b ≠ 2 := by omega
  have hne3 : b ≠ 3 := by omega
  simp [Heap.live, nonvacHeapInit, witnessHeap, Heap.empty, upd_ne, hne0, hne1, hne2, hne3]

private theorem nonvac_uniq : Zlib.Inflate.Spec.Uniq nonvacHeapInit := by
  intro b
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ 4 ≤ b) with rfl | rfl | rfl | rfl | hb
  · simp [Zlib.Inflate.Spec.cnt, nonvacHeapInit, witnessHeap, Heap.empty]
  · simp [Zlib.Inflate.Spec.cnt, nonvacHeapInit, witnessHeap, Heap.empty]
  · simp [Zlib.Inflate.Spec.cnt, nonvacHeapInit, witnessHeap, Heap.empty]
  · simp [Zlib.Inflate.Spec.cnt, nonvacHeapInit, witnessHeap, Heap.empty]
  · have hne0 : b ≠ 0 := by omega
    have hne1 : b ≠ 1 := by omega
    have hne2 : b ≠ 2 := by omega
    have hne3 : b ≠ 3 := by omega
    simp [Zlib.Inflate.Spec.cnt, nonvacHeapInit, witnessHeap, Heap.empty, upd_ne, hne0, hne1, hne2, hne3]

private theorem nonvac_fit : ZlibF.PlatformMemory.ByteObjectsFit nonvacHeapInit := by
  intro ref a hget
  have hsame : Space.get nonvacHeapInit ref = Space.get witnessHeap ref := by
    cases ref <;> rfl
  rw [hsame] at hget
  exact Zlib.Inflate.Proofs.inflate_default_witness_platform ref a hget

private theorem nonvac_domain : InitDomain nonvacHeapInit (.tab 0) (.ref (.blk 1) 0) := by
  refine ⟨nonvac_fresh, nonvac_uniq, rfl, ?_, default, rfl, ⟨Or.inl rfl, Or.inl rfl⟩, rfl⟩
  right
  refine ⟨49, rfl, Or.inr ⟨.blk 1, 0, #[49, 0], rfl, ?_, ?_, ?_⟩⟩
  · simp [Space.get, nonvacHeapInit, witnessHeap, Heap.empty]
  · decide
  · rfl

private theorem strTable_bounds : ∀ j : Fin strTable.size,
    (strBytes strTable[j]).size < ZlibF.PlatformMemory.byteObjectLimit := by
  decide +kernel

private theorem str_byteObjectFit (h : Heap) (i : Nat) (a : Array UInt8)
    (hget : Space.get h (BRef.str i) = some a) :
    a.size < ZlibF.PlatformMemory.byteObjectLimit := by
  rw [BRef.get_str] at hget
  unfold staticStringBytes at hget
  split at hget
  · rename_i hlt
    rw [Array.getElem?_eq_getElem hlt, Option.map_some] at hget
    cases hget
    exact strTable_bounds ⟨i, hlt⟩
  · cases he : h.libcErrorBorrow with
    | none => rw [he] at hget; cases hget
    | some p =>
      rcases p with ⟨epoch, e⟩
      rw [he] at hget
      dsimp only at hget
      split at hget
      · unfold C.libcErrnoTable at hget
        split at hget
        · rw [Option.map_some] at hget
          cases hget
          have hlt := C.LibcStrings.Proofs.errno_bytes_lt64 (UInt32.ofNat e.toUInt32.toNat).toInt32
          unfold ZlibF.PlatformMemory.byteObjectLimit; omega
        · cases hget
      · cases hget

private theorem byteObjectsFit_of_deflateInit {h after : Heap} {r : ZStreamRef} {p : Api.DeflParams}
    (hfit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (hinit : DeflateInitial h after r p) :
    ZlibF.PlatformMemory.ByteObjectsFit after := by
  obtain ⟨z', s', hgood, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hfr, hlc, _⟩ := hinit
  intro ref a hget
  have hkeep := hfr.2.2.2.2.2
  cases ref with
  | blk b =>
    rw [BRef.get_blk] at hget
    have hlive : after.live b := by simp [Heap.live, hget]
    rcases (hlc b).mp hlive with ⟨hlive_h, _⟩ | hown
    · by_cases hsr : StreamRoot r b
      · exfalso
        have hz : r.get after = some z' := hgood.live.hz
        cases r with
        | tab i =>
          cases hsr
          have e : after.streams b = some z' := hz
          have hne : after.streams b ≠ none := by rw [e]; exact Option.some_ne_none _
          obtain ⟨hb, _⟩ := (uniq_ne_none hgood.uniq).2.2.1 hne
          rw [hget] at hb; exact Option.some_ne_none _ hb
        | in_gzstate_strm i =>
          cases hsr
          cases hg : after.gzstates b with
          | none => simp [ZStreamRef.get, hg] at hz
          | some _ =>
            have hne : after.gzstates b ≠ none := by rw [hg]; exact Option.some_ne_none _
            obtain ⟨hb, _⟩ := (uniq_ne_none hgood.uniq).2.2.2.2.2.2 hne
            rw [hget] at hb; exact Option.some_ne_none _ hb
      · have hk := hkeep b hlive_h hsr
        have : h.bytes b = some a := hk.1.symm.trans hget
        exact hfit (.blk b) a (by rw [BRef.get_blk]; exact this)
    · obtain ⟨w, q, r_q, pb, hB⟩ := hgood.inv.blocks
      rcases hown with rfl | hw | hp | hq | hpb
      · have hne : after.dstates h.nextBlk ≠ none := by rw [hgood.live.hs]; exact Option.some_ne_none _
        obtain ⟨hb, _⟩ := (uniq_ne_none hgood.uniq).2.2.2.2.1 hne
        rw [hget] at hb; exact False.elim (Option.some_ne_none _ hb)
      · rw [hB.win] at hw; cases hw
        obtain ⟨wa, hwa, hws⟩ := hB.wa
        rw [hwa] at hget; cases hget
        have hws2 : s'.w_size.toNat = 2 ^ s'.w_bits.toNat := hgood.inv.wsize
        have hwb : s'.w_bits.toNat ≤ 15 := hgood.inv.wbits_hi
        have hp2 : 2 ^ s'.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) hwb
        unfold ZlibF.PlatformMemory.byteObjectLimit; omega
      · rw [hB.prev] at hp; cases hp
        obtain ⟨pa, hpa, _⟩ := hB.pa
        have hne : after.words b ≠ none := by rw [hpa]; exact Option.some_ne_none _
        obtain ⟨hb, _⟩ := (uniq_ne_none hgood.uniq).2.1 hne
        rw [hget] at hb; exact False.elim (Option.some_ne_none _ hb)
      · rw [hB.head] at hq; cases hq
        obtain ⟨qa, hqa, _⟩ := hB.qa
        have hne : after.words b ≠ none := by rw [hqa]; exact Option.some_ne_none _
        obtain ⟨hb, _⟩ := (uniq_ne_none hgood.uniq).2.1 hne
        rw [hget] at hb; exact False.elim (Option.some_ne_none _ hb)
      · rw [hB.pbuf] at hpb; cases hpb
        obtain ⟨ba, hba, hbs⟩ := hB.ba
        rw [hba] at hget; cases hget
        have hlit : 2 * s'.lit_bufsize.toNat = s'.hash_size.toNat := hgood.inv.lit
        have hhs : s'.hash_size.toNat = 2 ^ s'.hash_bits.toNat := hgood.inv.hsize
        have hhb : s'.hash_bits.toNat ≤ 16 := hgood.inv.hbits_hi
        have hp2 : 2 ^ s'.hash_bits.toNat ≤ 2 ^ 16 := Nat.pow_le_pow_right (by omega) hhb
        unfold ZlibF.PlatformMemory.byteObjectLimit; omega
  | dstate_depth i =>
    simp only [Space.get] at hget
    cases hd : after.dstates i with
    | none => simp [hd] at hget
    | some d' =>
      simp only [hd, Option.map_some, Option.some.injEq] at hget
      subst a
      have hlive : after.live i := by simp [Heap.live, hd]
      rcases (hlc i).mp hlive with ⟨hlive_h, _⟩ | hown
      · by_cases hsr : StreamRoot r i
        · exfalso
          have hz : r.get after = some z' := hgood.live.hz
          cases r with
          | tab j =>
            cases hsr
            have e : after.streams i = some z' := hz
            have hne : after.streams i ≠ none := by rw [e]; exact Option.some_ne_none _
            obtain ⟨_, _, _, hd', _⟩ := (uniq_ne_none hgood.uniq).2.2.1 hne
            rw [hd] at hd'; exact Option.some_ne_none _ hd'
          | in_gzstate_strm j =>
            cases hsr
            cases hg : after.gzstates i with
            | none => simp [ZStreamRef.get, hg] at hz
            | some _ =>
              have hne : after.gzstates i ≠ none := by rw [hg]; exact Option.some_ne_none _
              obtain ⟨_, _, _, _, hd', _⟩ := (uniq_ne_none hgood.uniq).2.2.2.2.2.2 hne
              rw [hd] at hd'; exact Option.some_ne_none _ hd'
        · have hk := hkeep i hlive_h hsr
          have hd_h : h.dstates i = some d' := hk.2.2.2.2.1.symm.trans hd
          exact hfit (.dstate_depth i) d'.depth (by simp [Space.get, hd_h])
      · obtain ⟨w, q, r_q, pb, hB⟩ := hgood.inv.blocks
        rcases hown with rfl | hw | hp | hq | hpb
        · rw [hgood.live.hs] at hd; cases hd
          rw [hgood.inv.wf.2.2.2.2.2]
          unfold ZlibF.PlatformMemory.byteObjectLimit; omega
        · rw [hB.win] at hw; cases hw
          obtain ⟨wa, hwa, _⟩ := hB.wa
          have hne : after.bytes i ≠ none := by rw [hwa]; exact Option.some_ne_none _
          obtain ⟨_, _, _, hd', _⟩ := (uniq_ne_none hgood.uniq).1 hne
          rw [hd] at hd'; exact False.elim (Option.some_ne_none _ hd')
        · rw [hB.prev] at hp; cases hp
          obtain ⟨pa, hpa, _⟩ := hB.pa
          have hne : after.words i ≠ none := by rw [hpa]; exact Option.some_ne_none _
          obtain ⟨_, _, _, hd', _⟩ := (uniq_ne_none hgood.uniq).2.1 hne
          rw [hd] at hd'; exact False.elim (Option.some_ne_none _ hd')
        · rw [hB.head] at hq; cases hq
          obtain ⟨qa, hqa, _⟩ := hB.qa
          have hne : after.words i ≠ none := by rw [hqa]; exact Option.some_ne_none _
          obtain ⟨_, _, _, hd', _⟩ := (uniq_ne_none hgood.uniq).2.1 hne
          rw [hd] at hd'; exact False.elim (Option.some_ne_none _ hd')
        · rw [hB.pbuf] at hpb; cases hpb
          obtain ⟨ba, hba, _⟩ := hB.ba
          have hne : after.bytes i ≠ none := by rw [hba]; exact Option.some_ne_none _
          obtain ⟨_, _, _, hd', _⟩ := (uniq_ne_none hgood.uniq).1 hne
          rw [hd] at hd'; exact False.elim (Option.some_ne_none _ hd')
  | str i =>
    exact str_byteObjectFit after i a hget
  | st_dist_code =>
    have hsame : Space.get after BRef.st_dist_code = Space.get h BRef.st_dist_code := by
      simp [Space.get, hfr.1]
    rw [hsame] at hget
    exact hfit .st_dist_code a hget
  | st_length_code =>
    have hsame : Space.get after BRef.st_length_code = Space.get h BRef.st_length_code := by
      simp [Space.get, hfr.1]
    rw [hsame] at hget
    exact hfit .st_length_code a hget

private theorem byteObjectsFit_of_inflateInit {h after : Heap} {r : ZStreamRef} {wrap : Api.Wrap} {bits : Nat}
    (hfit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (hinit : InflateInitial h after r wrap bits) :
    ZlibF.PlatformMemory.ByteObjectsFit after := by
  obtain ⟨z', s', hgood, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hfr, hlc⟩ := hinit
  intro ref a hget
  have hkeep := hfr.2.2.2.2.2
  cases ref with
  | blk b =>
    rw [BRef.get_blk] at hget
    have hlive : after.live b := by simp [Heap.live, hget]
    rcases (hlc b).mp hlive with ⟨hlive_h, _⟩ | rfl
    · by_cases hsr : StreamRoot r b
      · exfalso
        have hz : r.get after = some z' := hgood.live.hz
        cases r with
        | tab i =>
          cases hsr
          have e : after.streams b = some z' := hz
          have hne : after.streams b ≠ none := by rw [e]; exact Option.some_ne_none _
          obtain ⟨hb, _⟩ := (uniq_ne_none hgood.uniq).2.2.1 hne
          rw [hget] at hb; exact Option.some_ne_none _ hb
        | in_gzstate_strm i =>
          cases hsr
          cases hg : after.gzstates b with
          | none => simp [ZStreamRef.get, hg] at hz
          | some _ =>
            have hne : after.gzstates b ≠ none := by rw [hg]; exact Option.some_ne_none _
            obtain ⟨hb, _⟩ := (uniq_ne_none hgood.uniq).2.2.2.2.2.2 hne
            rw [hget] at hb; exact Option.some_ne_none _ hb
      · have hk := hkeep b hlive_h hsr
        exact hfit (.blk b) a (by rw [BRef.get_blk]; exact hk.1.symm.trans hget)
    · have hne : after.istates h.nextBlk ≠ none := by rw [hgood.live.hs]; exact Option.some_ne_none _
      obtain ⟨hb, _⟩ := (uniq_ne_none hgood.uniq).2.2.2.2.2.1 hne
      rw [hget] at hb; exact False.elim (Option.some_ne_none _ hb)
  | dstate_depth i =>
    simp only [Space.get] at hget
    cases hd : after.dstates i with
    | none => simp [hd] at hget
    | some d' =>
      simp only [hd, Option.map_some, Option.some.injEq] at hget
      subst a
      have hlive : after.live i := by simp [Heap.live, hd]
      rcases (hlc i).mp hlive with ⟨hlive_h, _⟩ | rfl
      · by_cases hsr : StreamRoot r i
        · exfalso
          have hz : r.get after = some z' := hgood.live.hz
          cases r with
          | tab j =>
            cases hsr
            have e : after.streams i = some z' := hz
            have hne : after.streams i ≠ none := by rw [e]; exact Option.some_ne_none _
            obtain ⟨_, _, _, hd', _⟩ := (uniq_ne_none hgood.uniq).2.2.1 hne
            rw [hd] at hd'; exact Option.some_ne_none _ hd'
          | in_gzstate_strm j =>
            cases hsr
            cases hg : after.gzstates i with
            | none => simp [ZStreamRef.get, hg] at hz
            | some _ =>
              have hne : after.gzstates i ≠ none := by rw [hg]; exact Option.some_ne_none _
              obtain ⟨_, _, _, _, hd', _⟩ := (uniq_ne_none hgood.uniq).2.2.2.2.2.2 hne
              rw [hd] at hd'; exact Option.some_ne_none _ hd'
        · have hk := hkeep i hlive_h hsr
          exact hfit (.dstate_depth i) d'.depth (by simp [Space.get, hk.2.2.2.2.1.symm.trans hd])
      · have hne : after.istates h.nextBlk ≠ none := by rw [hgood.live.hs]; exact Option.some_ne_none _
        obtain ⟨_, _, _, _, hd', _⟩ := (uniq_ne_none hgood.uniq).2.2.2.2.2.1 hne
        rw [hd] at hd'; exact False.elim (Option.some_ne_none _ hd')
  | str i =>
    exact str_byteObjectFit after i a hget
  | st_dist_code =>
    have hsame : Space.get after BRef.st_dist_code = Space.get h BRef.st_dist_code := by
      simp [Space.get, hfr.1]
    rw [hsame] at hget
    exact hfit .st_dist_code a hget
  | st_length_code =>
    have hsame : Space.get after BRef.st_length_code = Space.get h BRef.st_length_code := by
      simp [Space.get, hfr.1]
    rw [hsame] at hget
    exact hfit .st_length_code a hget

/-- `Goal.multi_stream_nonvacuity` -/
theorem multi_stream_nonvacuity : Goal.multi_stream_nonvacuity := by
  have hp6 : ∃ p, Api.deflInit? (6 : Int32).toInt (8 : Int32).toInt (15 : Int32).toInt
      (8 : Int32).toInt (0 : Int32).toInt = some p := ⟨_, rfl⟩
  obtain ⟨p6, hp6⟩ := hp6
  obtain ⟨h₀, _, init0, reach0⟩ :=
    ZlibF.Spec.Public.Proofs.DeflateInitDomain.deflate_domain_general
      nonvacHeapInit (.tab 0) (.ref (.blk 1) 0) 6 8 15 8 0 p6 nonvac_domain hp6 (fun _ _ => rfl)
  have hfit0 : ZlibF.PlatformMemory.ByteObjectsFit h₀ :=
    byteObjectsFit_of_deflateInit nonvac_fit init0
  have inv0 := streamInvariant_of_reach reach0
  obtain ⟨hf0, hu0, _⟩ := streamInvariant_facts inv0
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hfr0, _, _⟩ := init0
  have hg0 : LibraryGlobals h₀ := by
    unfold LibraryGlobals; rw [← hfr0.1]; rfl
  have hk3 : nonvacHeapInit.live 3 := by simp [Heap.live, nonvacHeapInit]
  have hk03 := hfr0.2.2.2.2.2 3 hk3 (by simp [StreamRoot])
  have hz3_0 : (ZStreamRef.tab 3).get h₀ = some default := by
    simp only [ZStreamRef.get]
    exact hk03.2.2.1.trans (by simp [nonvacHeapInit])
  have hv0 : VersionValue h₀ (.ref (.blk 1) 0) (some 49) := by
    have hk1 : nonvacHeapInit.live 1 := by simp [Heap.live, nonvacHeapInit, witnessHeap]
    have hk01 := hfr0.2.2.2.2.2 1 hk1 (by simp [StreamRoot])
    refine Or.inr ⟨49, rfl, Or.inr ⟨.blk 1, 0, #[49, 0], rfl, ?_, ?_, ?_⟩⟩
    · simp only [BRef.get_blk]
      exact hk01.1.trans (by simp [nonvacHeapInit, witnessHeap])
    · decide
    · rfl
  have ha0 : h₀.allocOk h₀.nalloc = true := by
    rw [← hfr0.2.1]; rfl
  obtain ⟨rc1, h₁, run1, _, hbr1⟩ :=
    (ZlibF.Spec.Public.Proofs.InflateInit.inflate_init2_public 15).2.2
      h₀ (.tab 3) default (.ref (.blk 1) 0) hf0 hu0 hg0 hz3_0 ⟨Or.inl rfl, Or.inl rfl⟩ hv0
  rw [ite_eq_right (by simp [ha0])] at hbr1
  have hw15 : Api.inflWbits (15 : Int32).toInt = some (.zlib, 15) := by decide
  rw [hw15] at hbr1
  obtain ⟨rfl, init1⟩ := hbr1
  have hfit1 : ZlibF.PlatformMemory.ByteObjectsFit h₁ :=
    byteObjectsFit_of_inflateInit hfit0 init1
  obtain ⟨reach0_1, reach1, disj1, _⟩ :=
    multi_stream_init_disjoint.1 h₀ h₁ (.tab 0) (.tab 3) default .deflate (.ref (.blk 1) 0) 15
      reach0 hg0 (by decide) hz3_0 ⟨Or.inl rfl, Or.inl rfl⟩ hv0 run1 (fun h => by cases h)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hfr1, _⟩ := init1
  have hg1 : LibraryGlobals h₁ := by
    unfold LibraryGlobals at hg0 ⊢; rw [← hfr1.1]; exact hg0
  have hext : ExternalWriteSafe h₁ (.tab 0) (.tab 3) (.deflateReset (some (.tab 0))) := by
    intro reg hm; simp [StreamWriteRegions] at hm
  obtain ⟨rc2, h₂, runStep, _, _, reach0_2, hreach1_2, _, _, _, disj2⟩ :=
    multi_stream_step_safety h₁ (.tab 0) (.tab 3) .deflate .inflate (.deflateReset (some (.tab 0)))
      reach0_1 reach1 hg1 disj1 hfit1 ⟨rfl, rfl⟩ trivial hext
  have inv0_1 := Zlib.Deflate.Universal.reachable_inv_of Zlib.Deflate.Universal.sequence_facts reach0_1
  obtain ⟨ds, z', d', dinv, _, _⟩ := inv0_1
  have good1 := dinv.good
  obtain ⟨d0, tb, tbuf, hB, -⟩ := good1.trees
  have e0 : d0 = d' := Option.some.inj (hB.dstate.symm.trans good1.live.hs)
  rw [e0] at hB
  obtain ⟨a1, a2, a3, eK, -, -, -, _, _⟩ :=
    Zlib.Deflate.Proofs.GeneralInit.resetKeep_initial good1.live hB good1.inv.wrap_lo good1.inv.wrap_hi
  obtain ⟨c1, c2, c3, _, e1, rfl, -, -, -, goodA, _⟩ :=
    Zlib.Deflate.Proofs.deflateResetKeep_safe good1
  have same := eK.symm.trans e1
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at same
  have states := congrArg (fun g : Heap => g.dstates ds) same
  simp only [Zlib.Deflate.Proofs.setD_dstates_same, Option.some.injEq] at states
  have l1 : a1 = c1 := congrArg DeflateState.dyn_ltree states
  have l2 : a2 = c2 := congrArg DeflateState.dyn_dtree states
  have l3 : a3 = c3 := congrArg DeflateState.bl_tree states
  subst l1 l2 l3
  obtain ⟨q, qa, h2', e2, hq, _, he, good2, _⟩ := Zlib.Deflate.Proofs.lm_init_safe goodA
  have runReset' : C.run (Zlib.Deflate.deflateReset (some (.tab 0))) h₁ = .ok (Z_OK, h2') := by
    have hz1 := goodA.live
    unfold Zlib.Deflate.deflateReset
    rw [C.run] at e1 ⊢
    simp only [bind_app, e1, beq_self_eq_true, ↓reduceIte, Zlib.Deflate.Proofs.zrd_eq,
      hz1.hz, hz1.zst, Zlib.Deflate.Proofs.castD, pure_app]
    rw [C.run] at e2; rw [e2]
  have eqStep := Except.ok.inj (runStep.symm.trans (Zlib.Deflate.Universal.heapCall_run runReset'))
  obtain ⟨-, rfl⟩ := eqStep
  have hfit2 : ZlibF.PlatformMemory.ByteObjectsFit h₂ := by
    have hst0 : h₁.streams 0 = some z' := good1.live.hz
    intro ref a hget
    cases ref with
    | blk b =>
      have hbytes : h₂.bytes = h₁.bytes := by
        simp [he, Zlib.Deflate.Spec.setD, Zlib.Deflate.Proofs.setW, ZStreamRef.put, hst0]
      rw [BRef.get_blk, hbytes] at hget
      exact hfit1 (.blk b) a (by rw [BRef.get_blk]; exact hget)
    | dstate_depth i =>
      simp only [Space.get] at hget
      cases hg_d : h₂.dstates i with
      | none => rw [hg_d] at hget; cases hget
      | some d2 =>
        rw [hg_d] at hget; simp only [Option.map_some, Option.some.injEq] at hget
        subst a
        by_cases hi : i = ds
        · subst i
          rw [good2.live.hs] at hg_d; cases hg_d
          rw [good2.inv.wf.2.2.2.2.2]
          unfold ZlibF.PlatformMemory.byteObjectLimit; omega
        · have hd_eq : h₂.dstates i = h₁.dstates i := by
            simp [he, Zlib.Deflate.Proofs.setW, Zlib.Deflate.Spec.setD, ZStreamRef.put, hst0,
              upd_ne _ _ _ _ hi]
          rw [hd_eq] at hg_d
          exact hfit1 (.dstate_depth i) d2.depth (by simp [Space.get, hg_d])
    | str i =>
      exact str_byteObjectFit h₂ i a hget
    | st_dist_code =>
      have hstat : h₂.static = h₁.static := by
        simp [he, Zlib.Deflate.Spec.setD, Zlib.Deflate.Proofs.setW, ZStreamRef.put, hst0]
      have hsame : Space.get h₂ BRef.st_dist_code = Space.get h₁ BRef.st_dist_code := by
        simp [Space.get, hstat]
      rw [hsame] at hget
      exact hfit1 .st_dist_code a hget
    | st_length_code =>
      have hstat : h₂.static = h₁.static := by
        simp [he, Zlib.Deflate.Spec.setD, Zlib.Deflate.Proofs.setW, ZStreamRef.put, hst0]
      have hsame : Space.get h₂ BRef.st_length_code = Space.get h₁ BRef.st_length_code := by
        simp [Space.get, hstat]
      rw [hsame] at hget
      exact hfit1 .st_length_code a hget
  exact ⟨h₀, h₁, h₂, .tab 0, .tab 3, reach0, reach0_1, reach1, disj1, hg1, hfit1, runReset',
    reach0_2, hreach1_2 (fun _ => hfit2), disj2⟩

#print axioms multi_stream_init_disjoint
#print axioms multi_stream_step_safety
#print axioms multi_stream_end_safety
#print axioms multi_stream_nonvacuity

end ZlibF.Spec.Public.MultiStreamProof
