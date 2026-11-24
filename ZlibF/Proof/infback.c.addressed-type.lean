import ZlibF.Proof.«infback.c.addressed-symbol»

/-! Choosing the block type from the addressed callback decoder's input. -/
namespace Zlib.Infback.AddressedType
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback.Proofs
open Zlib.Infback.Safety Zlib.Infback.AddressedStored

def selectMode (s : InflateState) (kind : UInt32) : InflateState :=
  match kind with
  | 0 => {s with mode := STORED}
  | 1 => {Zlib.Inftrees.Proofs.fixedState s with mode := LEN}
  | 2 => {s with mode := TABLE}
  | _ => {s with mode := BAD}

private def chooseAction (c : DecoderCtx) (kind : UInt32) : X Unit := do
  match kind with
  | 0 => setMode c.st STORED
  | 1 => Zlib.Inftrees.inflate_fixed c.st; setMode c.st LEN
  | 2 => setMode c.st TABLE
  | _ => badMode c "invalid block type"
  DROPBITS 2

/-- The final-block flag takes the DONE path without a refill. Otherwise a
successful refill supplies exactly the bits used for the last flag and mode.
An invalid type also writes the C error message. -/
theorem type_safe {owner w off cap : Nat} {cell : BPtrCell} {input : CInCb} {i : VoidPtr}
    {output : COutCb} {o : VoidPtr} {admitted : PointerLocals → Heap → Prop} {r : ZStreamRef}
    (cb : Callbacks owner w off cap cell input i output o admitted)
    (stream : ∀ cs H, admitted cs H → ∃ z, r.get H = some z)
    {s : InflateState} {l : IL} {h : Heap} (state : h.istates owner = some s)
    (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h) :
    let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
    if s.last != 0 then runX (back_TYPE c) l h = .ok ((.ok (), bytebits l), setI h owner {s with mode := DONE})
    else (∃ regs H, regs.ret = Z_BUF_ERROR ∧ runX (back_TYPE c) l h = .ok ((.error Ex.leave, regs), H) ∧
      AtExit owner w off cap cell r admitted s regs H) ∨
      (∃ regs H, runX (Zlib.Infback.NEEDBITS c 3) l h = .ok ((.ok (), regs), H) ∧
        Buffers cell w off cap s regs H ∧ admitted regs.pointerLocals H ∧ H.istates owner = some s ∧
        let marked := {s with last := u2i (bitsV regs 1)}
        let kind := bitsV (dropR regs 1) 2
        let ready := selectMode marked kind
        let post := dropR (dropR regs 1) 2
        (l.bits.toNat < 8 → l.hold.toNat < 2 ^ l.bits.toNat →
          post.bits.toNat < 8 ∧ post.hold.toNat < 2 ^ post.bits.toNat) ∧
        if kind < 3 then runX (back_TYPE c) l h = .ok ((.ok (), post), setI H owner ready)
        else ∃ z k, r.get H = some z ∧ strTable[k]? = some "invalid block type" ∧
          runX (back_TYPE c) l h = .ok ((.ok (), post),
            setI (r.put (setI H owner marked) {z with msg := .ref (.str k) 0}) owner ready)) := by
  let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
  have last : rdS c.st (·.last) h = .ok (s.last,h) := by
    rw [show c.st = some (.tab owner) from rfl, rdI_eq]; simp [state]
  by_cases final : (s.last != 0) = true
  · simp only [final, ↓reduceIte]
    have set : setMode c.st DONE h = .ok ((),setI h owner {s with mode := DONE}) := setMode_tab state DONE
    change runX (back_TYPE c) l h = _
    unfold back_TYPE
    simp only [runX_bind,runX_lift_ok last,final,↓reduceIte,BYTEBITS_run,runX_lift_ok set]; rfl
  · simp only [final, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨res, regs, H, need, valid, ok, present, count, err⟩ :=
      needBits_safe (strm := some r) cb 3 (by decide) state buf allowed
    change runX (Zlib.Infback.NEEDBITS c 3) l h = .ok ((res,regs),H) at need
    cases res with
    | error e =>
      obtain ⟨rfl,ret⟩ := err e rfl
      refine Or.inl ⟨regs,H,ret,?_,⟨present,valid,.caller ok⟩⟩
      change runX (back_TYPE c) l h = _
      unfold back_TYPE
      simp only [runX_bind,runX_lift_ok last,final,Bool.false_eq_true,↓reduceIte,need]
    | ok u =>
      cases u
      refine Or.inr ⟨regs,H,need,valid,ok,present,?_⟩
      let marked := {s with last := u2i (bitsV regs 1)}
      let middle := dropR regs 1
      let kind := bitsV middle 2
      let post := dropR middle 2
      have ⟨enough, bound, clean⟩ := count rfl
      change 3 ≤ regs.bits.toNat at enough
      change regs.bits.toNat ≤ max l.bits.toNat (3 + 7) at bound
      have rem1 : middle.bits.toNat = regs.bits.toNat - 1 :=
        dropR_bits (show (1 : UInt32).toNat ≤ regs.bits.toNat by change 1 ≤ _; omega)
      have fit2 : (2 : UInt32).toNat ≤ middle.bits.toNat := by change 2 ≤ _; omega
      have rem2 : post.bits.toNat = middle.bits.toNat - 2 := dropR_bits fit2
      refine ⟨fun small held => ⟨by change post.bits.toNat < 8; omega,
        dropR_clean (by decide) fit2 (dropR_clean (by decide) (by change 1 ≤ regs.bits.toNat; omega) (clean held))⟩, ?_⟩
      have base : (setI H owner marked).istates owner = some marked := upd_same ..
      have mark : wrS c.st (fun t => {t with last := u2i (bitsV regs 1)}) H = .ok ((),setI H owner marked) :=
        wrS_tab present _
      have bit1 : runX (BITS 1) regs H = .ok ((.ok (bitsV regs 1),regs),H) := BITS_run _ _ _ (by decide)
      have drop1 : ∀ h, runX (DROPBITS 1) regs h = .ok ((.ok (),middle),h) := fun _ => DROPBITS_run _ _ _ (by decide)
      have bit2 : ∀ h, runX (BITS 2) middle h = .ok ((.ok kind,middle),h) := fun _ => BITS_run _ _ _ (by decide)
      have drop2 : ∀ h, runX (DROPBITS 2) middle h = .ok ((.ok (),post),h) := fun _ => DROPBITS_run _ _ _ (by decide)
      have bound : kind.toNat < 4 := bitsV_lt middle (k := 2) (by decide)
      have cases' : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by
        have : kind.toNat = 0 ∨ kind.toNat = 1 ∨ kind.toNat = 2 ∨ kind.toNat = 3 := by omega
        rcases this with h | h | h | h
        · exact Or.inl (UInt32.toNat_inj.mp h)
        · exact Or.inr (Or.inl (UInt32.toNat_inj.mp h))
        · exact Or.inr (Or.inr (Or.inl (UInt32.toNat_inj.mp h)))
        · exact Or.inr (Or.inr (Or.inr (UInt32.toNat_inj.mp h)))
      have choose : runX (back_TYPE c) l h = runX (chooseAction c kind) middle (setI H owner marked) := by
        unfold back_TYPE
        simp only [runX_bind,runX_lift_ok last,final,Bool.false_eq_true,↓reduceIte,need,bit1,runX_lift_ok mark,drop1,bit2]
        rfl
      have mode (n : UInt32) : setMode c.st n (setI H owner marked) = .ok ((),setI (setI H owner marked) owner {marked with mode := n}) :=
        setMode_tab base n
      change if kind < 3 then runX (back_TYPE c) l h = .ok ((.ok (),post),setI H owner (selectMode marked kind)) else _
      rcases cases' with k | k | k | k
      · rw [k] at choose ⊢
        simp only [show (0 : UInt32) < 3 by decide,↓reduceIte,selectMode,choose,chooseAction,runX_bind,runX_lift_ok (mode STORED),drop2,setI_setI]
      · rw [k] at choose ⊢
        let fixed := Zlib.Inftrees.Proofs.fixedState marked
        have fix : Zlib.Inftrees.inflate_fixed c.st (setI H owner marked) = .ok ((),setI (setI H owner marked) owner fixed) :=
          Zlib.Inftrees.Proofs.inflate_fixed_ok base
        have st : (setI H owner fixed).istates owner = some fixed := upd_same ..
        have dest : setMode c.st LEN (setI H owner fixed) = _ := setMode_tab st LEN
        simp only [show (1 : UInt32) < 3 by decide,↓reduceIte,selectMode,choose,chooseAction,runX_bind,runX_lift_ok fix,runX_lift_ok dest,drop2,setI_setI]
        rfl
      · rw [k] at choose ⊢
        simp only [show (2 : UInt32) < 3 by decide,↓reduceIte,selectMode,choose,chooseAction,runX_bind,runX_lift_ok (mode TABLE),drop2,setI_setI]
      · obtain ⟨z,live⟩ := stream _ _ ok
        have live' : r.get (setI H owner marked) = some z := by simpa using live
        obtain ⟨j,text,bad⟩ := badMode_ctx_literal c rfl rfl live' base _ lit_invalid_block_type
        rw [k] at choose ⊢
        simp only [show ¬(3 : UInt32) < 3 by decide,↓reduceIte]
        refine ⟨z,j,live,text,?_⟩
        rw [choose]
        change runX (do liftM (badMode c "invalid block type"); DROPBITS 2 : X Unit) middle (setI H owner marked) = _
        simp only [runX_bind,runX_lift_ok bad,drop2]
        let H' := r.put (setI H owner marked) {z with msg := .ref (.str j) 0}
        change (Except.ok ((Except.ok (),post),setI H' owner {marked with mode := BAD}) :
          Except Fault ((Except Ex Unit × IL) × Heap)) = .ok ((.ok (),post),setI H' owner (selectMode marked kind))
        rw [k]; rfl

#print axioms type_safe
end Zlib.Infback.AddressedType
