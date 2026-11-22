import ZlibF.Spec.Common.GzInv
import ZlibF.Spec.Functional.GzControl
import ZlibF.Spec.Functional.Api.Compress
import ZlibF.Proof.«gzlib.c.base»

/-!
# gz file interface, safety: the representation invariant `GzInv` and the shape of a safe call

The shared definitions of the gz safety proof, over the OS-call oracle of `ZlibF/Zlib/gzfs.lean`:

1. `GzInv` (`GzCommon`, `GzReadInv`, `GzWriteInv`): the representation invariant of an open handle, with the
   write clauses W1–W10 folded into the write part. Other modules use its interface lemmas, not the definition.
2. `GzCallSafe`: safety of one public call on a handle in `GzInv`, for every world.
3. `ReadsFinite`: the M7 premise of the termination half of the reading calls: the descriptor is non-negative and
   has a read budget below `2^61` bytes in the OS-call oracle (`Fs.readBudget`).

Clauses that the proofs need:
- `GzCommon.next` also excludes the message block (`blkOf s.msg ≠ some b`), as `NextOk` does. Without it `x.next`
  may point into the message block, which `gz_error` frees, so `GzInv` would not survive `gz_error`.
- With no codec set up (`GzReadInv.unalloc`, W2, W8) `strm.state` is NULL. "The codec owns no block" would let
  `strm.state` name a block that is not live, which a caller may then allocate, so `GzInv.caller` would be false.
- `GzCommon.recordFree`: the codec does not own the record block, so that a write of the record (`put_scalars`,
  `gz_error`) is a rebuffer of the codec.
- `GzReadInv.posHave`: `x.pos + x.have ≤ GZ_OFF_MAX` on return (patch 0003). Without it the buffered path of
  `gzgetc` overflows `x.pos`.
- `GzReadInv.againSize`: `size = 0 → again = 0`. Without it `gzungetc` computes `out + 2·size - 1` on a NULL `out`.
- `GzReadInv.haveSkip`: `x.have ≠ 0 → skip = 0` at call boundaries; `GzInvUpToSkip` is the invariant without it, for
  the inside of reading calls. Without it `gzgetc` returns a buffered byte while a skip is pending, and moves `x.pos`
  past `GZ_OFF_MAX - skip`.
- `GzPost` has a no-grab clause: a block owned after a helper call was owned before it or was not live before it.

Patches. Some clauses (`GzCommon.pos`, `GzCommon.next`, `GzReadInv.output`) are established only for the patched
source (patches 0002, 0003 and 0004). The definitions do not depend on that;
the lemmas that need a patch say so.
-/

namespace ZlibF.Spec.Public
open C Zlib.GzFs
set_option autoImplicit false

/-! ## The shape of a safe call -/

/-- **Safety of one call** on a handle in `GzInv`, for every world (every oracle): no fault other than running
out of fuel; it returns, under M7 for the calls that need it; and when it returns the open descriptors are kept
and `GzStepPost` holds. -/
def GzCallSafe (i : Nat) (call : Call) : Prop :=
  ∀ h fs s, GzInv h i s → FileSystem fs → GzArguments h i s call →
    (∀ e, call.execute fs h = .error e → e = .outOfFuel) ∧
    ((NeedsReadBound call → ReadsFinite fs s.fd) →
      ∃ value fs' after, call.execute fs h = .ok ((value, fs'), after)) ∧
    (∀ value fs' after, call.execute fs h = .ok ((value, fs'), after) →
      FdsKept fs fs' ∧ GzStepPost h i s call fs' after)

/-! ## Helper shapes for the internal call lemmas -/

/-- The three parts of a run in `G` that a safety lemma states: no fault but `outOfFuel`; a result under the
premise `finite` (M7 where needed, `True` otherwise); and `post` of every result. -/
def RunSafe {α : Type} (m : G α) (fs : Fs) (h : Heap) (finite : Prop) (post : α → Fs → Heap → Prop) : Prop :=
  (∀ e, m fs h = .error e → e = .outOfFuel) ∧
  (finite → ∃ a fs' after, m fs h = .ok ((a, fs'), after)) ∧
  (∀ a fs' after, m fs h = .ok ((a, fs'), after) → post a fs' after)

/-- `GzStepPost` with explicit caller regions (for the internal helpers), and no grab: every block the handle owns
after the call was owned before it, or was not live before it. The last clause lets two helper calls compose with
an exact ledger (`gz_look` then `gz_skip` in `gzungetc`; `gz_read` then a free in `gzgetc`). -/
def GzPost (h : Heap) (i : Nat) (s : GzState) (regions : List Region) (fs' : Fs) (after : Heap)
    (inv : Heap → Nat → GzState → Prop) : Prop :=
  FileSystem fs' ∧ ∃ s', inv after i s' ∧ s'.mode = s.mode ∧ s'.fd = s.fd ∧
    BufferFrame h after (GzOwned h i s) regions ∧
    LiveChange h after
      (fun b => GzOwned after i s' b ∧ ¬ h.live b)
      (fun b => GzOwned h i s b ∧ ¬ GzOwned after i s' b) ∧
    (∀ b, GzOwned after i s' b → GzOwned h i s b ∨ ¬ h.live b)

/-- The record with no buffered output (`x.have = 0`, `x.next = NULL`). -/
def clearOut (s : GzState) : GzState := { s with x := { s.x with «have» := 0, next := .null } }

/-- **The invariant up to the buffered output**, for the inside of a reading call: `GzInv` of the record with no
buffered output. `gz_decomp` and `gz_load` into the caller's buffer leave `x.next` in that buffer; `GzInv` allows
that once `x.have = 0` (`GzCommon.next`), and this is what holds before `x.have` is reset. -/
def GzInvUpToOutput (h : Heap) (i : Nat) (s : GzState) : Prop :=
  h.gzstates i = some s ∧ GzInv (putGz h i (clearOut s)) i (clearOut s)

/-- The record with no pending skip. -/
def clearSkip (s : GzState) : GzState := { s with skip := 0 }

/-- **The invariant up to the pending skip**, for the inside of a reading call: `GzInv` without the clause
`GzReadInv.haveSkip`. It is `GzInv` of the record with no pending skip, plus the bounds of `GzCommon.pos` on the
skip. `gz_look` (COPY) and `gz_fetch` (from `gz_skip`) may buffer output while a skip is pending; the caller
(`gz_skip`, `gzungetc`, `gzdirect`) consumes it before it returns. -/
def GzInvUpToSkip (h : Heap) (i : Nat) (s : GzState) : Prop :=
  h.gzstates i = some s ∧ GzInv (putGz h i (clearSkip s)) i (clearSkip s) ∧
    0 ≤ s.skip.toInt ∧ s.x.pos.toInt + s.skip.toInt ≤ 9223372036854775807

/-! ## Interface lemmas of `GzInv` -/

/-- The state pointer of handle `i`. -/
def gzSt (i : Nat) : GzStatePtr := some (.tab i)

/-- Interface: the common part. -/
theorem GzInv.common {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) : GzCommon h i s := And.left inv

/-- Interface: the reader part. -/
theorem GzInv.reader {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hm : s.mode = GZ_READ) :
    GzReadInv h i s := (And.right inv).1 hm

/-- Interface: the writer part. -/
theorem GzInv.writer {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hm : s.mode = GZ_WRITE) :
    GzWriteInv h i s := (And.right inv).2 hm

/-- Interface: the record determines the state. -/
theorem GzInv.state_eq {h : Heap} {i : Nat} {s t : GzState} (inv : GzInv h i s) (ht : h.gzstates i = some t) :
    s = t := by
  have hs := inv.common.record
  rw [ht] at hs
  exact (Option.some.inj hs).symm

/-- Interface: the old lower bound of the position, `-(2·size) ≤ x.pos`, follows from `GzCommon.pos` (for a writer
`x.have = 0`, for a reader `x.have ≤ 2·size`). -/
theorem GzInv.pos_lower {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) :
    -(2 * s.size.toNat : Int) ≤ s.x.pos.toInt := by
  have hlo := inv.common.pos.2.2
  have hhave : s.x.have.toNat ≤ 2 * s.size.toNat := by
    rcases inv.common.mode with hm | hm
    · by_cases hz : s.x.have = 0
      · rw [hz]; exact Nat.zero_le _
      · obtain ⟨c, _, hle⟩ := (inv.reader hm).output hz
        omega
    · rw [(inv.writer hm).have0]; exact Nat.zero_le _
  omega

/-- Interface: with `strm.state = NULL` the codec owns no block. -/
theorem noCodec_owned {h : Heap} {i : Nat} {s : GzState} (hs : h.gzstates i = some s)
    (hn : s.strm.state = none) (b : Nat) : ¬ StreamOwned h (gzStrm i) b := by
  rintro ⟨z, hz, ⟨k, st, hk, _, _⟩ | ⟨k, d, hk, _, _⟩⟩
  all_goals
    simp [ZStreamRef.get, gzStrm, hs] at hz
    subst hz
    rw [hn] at hk
    cases hk

/-! ## Decision (4): the three `Uniq` are one predicate -/

/-- `Zlib.Gzlib.Spec.Uniq` and `Zlib.Inflate.Spec.Uniq` have the same body (one object per block number over the
same seven tables), so the codec histories embed with no conversion. -/
theorem gz_uniq_iff_inflate (h : Heap) : Zlib.Gzlib.Spec.Uniq h ↔ Zlib.Inflate.Spec.Uniq h := Iff.rfl

/-- The same for `Zlib.Deflate.Spec.Uniq`. -/
theorem gz_uniq_iff_deflate (h : Heap) : Zlib.Gzlib.Spec.Uniq h ↔ Zlib.Deflate.Spec.Uniq h := Iff.rfl

end ZlibF.Spec.Public
