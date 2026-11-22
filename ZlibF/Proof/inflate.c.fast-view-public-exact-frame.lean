import ZlibF.Proof.«inflate.c.fast-view-env»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual fast call's output interval is framed within the entry caller
output slice `[⟨slow.put, slow.left.toNat⟩]` while reporting the exact public
produced byte count. -/
theorem inflate_fast_default_view_public_exact_frame
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (mode : s.mode = LEN)
    (inputCursor : z.next_in = slow.next)
    (inputCount : z.avail_in = slow.have_)
    (outputCursor : z.next_out = slow.put)
    (outputCount : z.avail_out = slow.left)
    (stateHold : s.hold = slow.hold)
    (stateBits : s.bits = slow.bits)
    (fast : (slow.have_ >= 6 && slow.left >= 258 &&
      slow.bits < 8) = true) :
    ∃ finished zNext sNext used produced,
      C.run (Zlib.Inffast.inflate_fast (some r) slow.out_) h =
        .ok ((), finished) ∧
      DefaultStateJ finished r zs zNext sNext ∧
      StreamAccounting z zNext used produced ∧
      BufferFrame h finished (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, slow.left.toNat⟩] := by
  obtain ⟨finished, zNext, sNext, used, made, _, _, run, current, accounting,
    _, _, _, _, _, _, _, _, _, _, _, _, frame⟩ :=
    fast_view_exec invariant buffers mode inputCursor inputCount
      outputCursor outputCount stateHold stateBits fast
  exact ⟨finished, zNext, sNext, used, made, run, current, accounting, frame⟩

#print axioms inflate_fast_default_view_public_exact_frame

end Zlib.Inflate.Proofs
