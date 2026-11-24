import ZlibF.Proof.«infback.c.addressed-fast»
import ZlibF.Proof.«infback.c.addressed-type»
import ZlibF.Proof.«infback.c.addressed-dynamic»

/-! The dispatcher's literal/length entry, including both the fast and slow decoder. -/
namespace Zlib.Infback.AddressedTable
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback.Proofs Zlib.Infback.Safety
open Zlib.Infback.AddressedStored ZlibF.Spec.Public
set_option autoImplicit false

/-- The mode read and switch select exactly the computed LEN round, including
callback refusals. A continuing round publishes a mode for the next switch. -/
theorem dispatch_len {owner w off cap : Nat} {cell : BPtrCell} {input : CInCb} {i : VoidPtr}
    {output : COutCb} {o : VoidPtr} {admitted : PointerLocals → Heap → Prop} {r : ZStreamRef}
    (cb : Callbacks owner w off cap cell input i output o admitted)
    (edit : ∀ cs H t, admitted cs H → admitted cs (setI H owner t))
    (stream : ∀ cs H, admitted cs H → ∃ z, r.get H = some z)
    (globals : ∀ cs H, admitted cs H → LibraryGlobals H)
    {s : InflateState} {l : IL} {h : Heap} {z : ZStream}
    (live : r.get h = some z) (index : z.state = some (.inflate owner)) (get : h.istates owner = some s)
    (buf : Buffers cell w off cap s l h) (ok : admitted l.pointerLocals h)
    (mode : s.mode = LEN) (tabs : TablesOk owner s) (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (state : StOk s) (winSize : s.wsize.toNat ≤ 32768)
    (short : l.bits.toNat < 8) (held : l.hold.toNat < 2 ^ l.bits.toNat) :
    let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
    LenResult owner (runX (back_dispatch c) l h) := by
  let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
  have rd : rdS c.st (·.mode) h = .ok (LEN, h) := by
    change rdS (some (.tab owner)) _ h = _
    simp only [rdI_eq, get, mode]
  change LenResult owner (runX (back_dispatch c) l h)
  rw [back_dispatch, runX_bind, runX_lift_ok rd]
  exact len_case cb edit stream globals live index get buf ok mode tabs fit state winSize short held

/-- A valid TABLE switch executes the complete dynamic builder and the LEN
fallthrough against the same callback state, including the actual fast-call result. -/
theorem dispatch_table {owner w off cap : Nat} {cell : BPtrCell} {input : CInCb} {i : VoidPtr}
    {output : COutCb} {o : VoidPtr} {admitted : PointerLocals → Heap → Prop} {r : ZStreamRef}
    (cb : Callbacks owner w off cap cell input i output o admitted)
    (edit : ∀ cs H t, admitted cs H → admitted cs (setI H owner t))
    (stream : ∀ cs H, admitted cs H → ∃ z, r.get H = some z ∧ z.state = some (.inflate owner))
    (globals : ∀ cs H, admitted cs H → LibraryGlobals H)
    (fit : ∀ cs H, admitted cs H → ZlibF.PlatformMemory.ByteObjectsFit H)
    {s : InflateState} {l : IL} {h : Heap} (get : h.istates owner = some s)
    (buf : Buffers cell w off cap s l h) (ok : admitted l.pointerLocals h)
    (mode : s.mode = TABLE) (wf : s.WellFormed) (state : StOk s)
    (size : cap ≤ 32768) (bits : ReadyBits l) :
    let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
    LenResult owner (runX (back_dispatch c) l h) := by
  let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
  have live cs H (ok : admitted cs H) : ∃ z, r.get H = some z := by
    obtain ⟨z, rd, _⟩ := stream cs H ok
    exact ⟨z, rd⟩
  have rd : rdS c.st (·.mode) h = .ok (TABLE,h) := by
    change rdS (some (.tab owner)) _ h = _
    simp only [rdI_eq, get, mode]
  change LenResult owner (runX (back_dispatch c) l h)
  rw [back_dispatch, runX_bind, runX_lift_ok rd]
  change LenResult owner (runX (back_TABLE c) l h)
  rcases dynamic_safe cb (DynamicFrame.of_private live edit) get buf ok mode wf with empty | bad | built
  · obtain ⟨regs,H,ret,run,_⟩ := empty
    exact Or.inl ⟨regs,H,run,ret⟩
  · obtain ⟨regs,H,t,st,target,run,_⟩ := bad
    exact Or.inr ⟨regs,H,t,run,st,Or.inr (Or.inr target)⟩
  · obtain ⟨regs,H,t,st,len,_,tables,buffer,admit,kept,⟨_,safe⟩,cut⟩ := built
    obtain ⟨z,atZ,index⟩ := stream _ _ admit
    rw [cut]
    exact len_case cb edit live globals atZ index st buffer admit len tables (fit _ _ admit)
      (safe state)
      (by rw [buffer.size]; exact size) (kept bits).1 (kept bits).2

#print axioms dispatch_table
#print axioms dispatch_len
end Zlib.Infback.AddressedTable
