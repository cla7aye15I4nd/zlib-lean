import ZlibF.Proof.«inflate.c.main.table4»
import ZlibF.Proof.«inftrees.c»

/-!
# inflate.c: `case LENLENS:` -- the `inflate_table(CODES, ...)` call and what follows
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
open Zlib.Inftrees (inflate_table)

/-- Storing the arrays `work` and `codes` of the state record. -/
theorem put_work_codes {h : Heap} {zs : Nat} {s : InflateState} (e : h.istates zs = some s) (wa : Array UInt16)
    (ca : Array Code) :
    Space.put (Space.put h (WRef.istate_work zs) wa) (CodeRef.istate_codes zs) ca =
      setI h zs { s with work := wa, codes := ca } := by
  rw [WRef.put_istate_work e wa]
  have e2 : ({ h with istates := upd h.istates zs (some { s with work := wa }) } : Heap).istates zs =
      some { s with work := wa } := by simp
  rw [CodeRef.put_istate_codes e2 ca]
  simp [setI, upd_upd]

/-- The state record after `state->next = state->codes; state->lencode = state->distcode = state->next; state->lenbits = 7`. -/
def llPre (zs : Nat) (s : InflateState) : InflateState :=
  { s with next := .ref (.istate_codes zs) 0, distcode := .ref (.istate_codes zs) 0, lencode := .ref (.istate_codes zs) 0, lenbits := 7 }

/-- The state record after a successful table call: `next` moved, `lenbits` as the call left it, `work` and `codes` changed;
`have = 0`, `mode = CODELENS`. -/
def llOkSt (zs : Nat) (s : InflateState) (u : Nat) (lb : UInt32) (wa : Array UInt16) (ca : Array Code) : InflateState :=
  { llPre zs s with next := .ref (.istate_codes zs) u, lenbits := lb, work := wa, codes := ca, «have» := 0, mode := CODELENS }

theorem eta_next_lenbits (x : InflateState) (n : CodePtr) (b : UInt32) (hn : x.next = n) (hb : x.lenbits = b) :
    { x with next := n, lenbits := b } = x := by
  cases x; simp_all

/-- The state record when the table call rejected the lengths (before `BAD` is set). -/
def llBadSt (zs : Nat) (s : InflateState) (wa : Array UInt16) (ca : Array Code) : InflateState :=
  { llPre zs s with work := wa, codes := ca }

end Zlib.Inflate.Proofs
