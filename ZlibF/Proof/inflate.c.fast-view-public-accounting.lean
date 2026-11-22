import ZlibF.Proof.«inflate.c.fast-view-env»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec Zlib.Inffast.Proofs
set_option autoImplicit false

/-- The complete translated fast call accounts for byte movements against
the original public stream, including every broken decoder exit. -/
theorem inflate_fast_default_view_accounting
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
      Good finished r zs zNext sNext ∧
      StreamAccounting z zNext used produced := by
  obtain ⟨finished, zNext, sNext, used, made, _, _, run, current, accounting, _⟩ :=
    fast_view_exec invariant buffers mode inputCursor inputCount
      outputCursor outputCount stateHold stateBits fast
  exact ⟨finished, zNext, sNext, used, made, run, current.good, accounting⟩

/-- The actual fast call simultaneously retains the initialized decoder
relation and accounts for bytes against its entry stream. -/
theorem inflate_fast_default_view_public_core
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
      StreamAccounting z zNext used produced := by
  obtain ⟨finished, zNext, sNext, used, made, _, _, run, current, accounting, _⟩ :=
    fast_view_exec invariant buffers mode inputCursor inputCount
      outputCursor outputCount stateHold stateBits fast
  exact ⟨finished, zNext, sNext, used, made, run, current, accounting⟩

#print axioms inflate_fast_default_view_accounting
#print axioms inflate_fast_default_view_public_core
end Zlib.Inflate.Proofs
