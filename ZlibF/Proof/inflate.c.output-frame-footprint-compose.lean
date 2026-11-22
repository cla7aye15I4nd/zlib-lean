import ZlibF.Proof.«inflate.c.window-pointer-run»
import ZlibF.Proof.«inflate.c.caller-input-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem inflate_buffer_frame_mono {h after : Heap} {small large : Nat → Prop} {regions : List Region}
    (frame : BufferFrame h after small regions) (included : ∀ b, small b → large b) :
    BufferFrame h after large regions := ⟨inflate_frame_mono frame.1 included, frame.2⟩

theorem frame_byte_view_ro {h after : Heap} {changed : Nat → Prop}
    {ref : BRef} {array : Array UInt8} {off : Nat}
    (frame : Frame h after changed) (get : Space.get h ref = some array)
    (outside : ∀ b, ByteRoot (.ref ref off) b → ¬ changed b) : Space.ro after ref = Space.ro h ref := by
  cases ref with
  | blk b =>
    have live : h.live b := by simp [Heap.live, show h.bytes b = some array from get]
    exact (frame.2.2.2.2.2 b live (outside b rfl)).2.2.2.2.2.2.2
  | dstate_depth _ | str _ | st_dist_code | st_length_code => rfl

/-- The caller's admitted byte view is outside the stream and the incoming
owned decoder storage. Mutability does not change the ownership argument. -/
theorem caller_byte_root_outside_writing {h : Heap} {r : ZStreamRef} {zs off count b : Nat}
    {z : ZStream} {s : InflateState} {ref : BRef} {array : Array UInt8} {writing : Bool}
    (good : Good h r zs z s) (get : Space.get h ref = some array)
    (range : CallerRange h r (.ref ref off) count writing) (root : ByteRoot (.ref ref off) b) :
    ¬ (StreamRoot r b ∨ InflateOwned zs s b) := by
  rcases range with null | ⟨_, _, outside⟩
  · cases null
  · rintro (stream | owned)
    · exact caller_byte_root_not_stream good get root stream
    · exact outside b root ((good.streamOwned_iff b).mpr owned)

/-- Private leave/window writes retain the caller's full output byte view
and its mutability, even when the output slice is empty. -/
theorem inflate_leave_output_view_unchanged {c : Ctx} {l : IL} {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} {rc : Int32} {ref : BRef} {off : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (run : inflate_leave c l h = .ok (rc, after)) (pointer : l.put = .ref ref off)
    (get : Space.get h ref = some array) :
    Frame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b) ∧
    Space.get after ref = some array ∧ Space.ro after ref = Space.ro h ref := by
  have frame := inflate_leave_frame_public E invariant allocator buffers bits run
  have range : CallerRange h r (.ref ref off) l.left.toNat true := by rw [← pointer]; exact buffers.output.range
  have outside := fun b root => caller_byte_root_outside_writing invariant.good get range (b := b) root
  have persistent : C.LibcBorrow.PersistentView ref := by
    cases ref with
    | str i =>
      rcases range with impossible | ⟨_, writable, _⟩
      · cases impossible
      · rcases writable rfl with ⟨impossible, _⟩ | ⟨ref', off', a', ptr, _, ro, _⟩
        · cases impossible
        · cases ptr
          simp [Space.ro] at ro
    | _ => trivial
  exact ⟨frame, BorrowedViews.frame_get_persistent frame get outside persistent,
    frame_byte_view_ro frame get outside⟩

end Zlib.Inflate.Proofs
