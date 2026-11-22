import ZlibF.Proof.«inflate.c.control-rank»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual dictionary-id mode leaves immediately when its word is incomplete. -/
theorem inflate_DICTID_wait {c : Ctx} {h : Heap} {l current : IL} {exit : Ex}
    (pull : runX (NEEDBITS 32) l h = .ok ((.error exit, current), h)) :
    runX (inflate_DICTID c) l h = .ok ((.error exit, current), h) := by
  unfold inflate_DICTID
  rw [runX_bind, pull]

/-- After the actual word read, DICTID writes the swapped checksum,
clears the local bit buffer and enters the real DICT continuation. -/
theorem inflate_DICTID_parsed_cut {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l current : IL)
    (pull : runX (NEEDBITS 32) l h = .ok ((.ok (), current), h)) :
    runX (inflate_DICTID c) l h = runX (inflate_DICT c) { current with hold := 0, bits := 0 }
      (setI (r.put h { z with adler := ZSWAP32 current.hold }) zs
        { s with check := ZSWAP32 current.hold, mode := DICT }) := by
  let value := ZSWAP32 current.hold
  unfold inflate_DICTID
  rw [runX_bind, pull]
  simp only []
  rw [runX_bind, runX_get]
  simp only []
  rw [runX_bind, runX_wrS E]
  simp only []
  have E1 : Env c (setI h zs { s with check := value }) r zs z { s with check := value } :=
    ⟨E.strm, E.st, by simpa only [ZStreamRef.get_setI] using E.hz, by simp⟩
  have write : wrZ c.strm (fun stream => { stream with adler := value }) (setI h zs { s with check := value }) =
      .ok ((), setI (r.put h { z with adler := value }) zs { s with check := value }) := by
    simp only [E.strm, wrZ_eq, E1.hz, ZStreamRef.put_setI]
  rw [runX_bind, runX_lift_ok write]
  simp only []
  rw [runX_bind, runX_INITBITS]
  simp only []
  have E2 : Env c (setI (r.put h { z with adler := value }) zs { s with check := value }) r zs
      { z with adler := value } { s with check := value } :=
    ⟨E.strm, E.st, by rw [ZStreamRef.get_setI]; exact ZStreamRef.get_put_same E.hz _, by simp⟩
  rw [runX_bind, runX_setMode E2, setI_setI]

end Zlib.Inflate.Proofs
