import ZlibF.Proof.«inflate.c.register-frame»
import ZlibF.Zlib.«infback.c»

/-! # The current Huffman code across input callbacks and bit consumption -/
namespace Zlib.Infback.CodeFrame
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback

abbrev KeepsCode (code : Code) (op : X α) : Prop := RegisterFrame (fun l => l.here = code) op

private theorem pull_ctx (c : DecoderCtx) (base : Code) (input : ∀ next, KeepsCode base (c.input next)) : KeepsCode base (Zlib.Infback.PULL c) := by
  unfold Zlib.Infback.PULL
  apply registerFrame_get_bind
  intro l same
  split
  · refine registerFrame_bind (input l.next) ?_
    rintro ⟨n, next⟩
    apply registerFrame_get_bind
    intro regs fixed
    register_frame_source
  · exact registerFrame_pure (fun regs => regs.here = base) ()

theorem pull (c : BCtx) (base : Code) : KeepsCode base (Zlib.Infback.PULL c) :=
  pull_ctx c base fun next => registerFrame_lift _ (c.inCb c.inDesc next)

theorem absorb (base : Code) : KeepsCode base absorbInputByte := by
  unfold absorbInputByte
  register_frame_source

theorem need_ctx (c : DecoderCtx) (base : Code) (input : ∀ next, KeepsCode base (c.input next)) (n : UInt32) : KeepsCode base (Zlib.Infback.NEEDBITS c n) := by
  unfold Zlib.Infback.NEEDBITS Zlib.Infback.PULLBYTE
  apply registerFrame_xwhile
  · register_frame_source
  · exact registerFrame_bind (pull_ctx c base input) fun _ => absorb base

theorem need (c : BCtx) (base : Code) (n : UInt32) : KeepsCode base (Zlib.Infback.NEEDBITS c n) :=
  need_ctx c base (fun next => registerFrame_lift _ (c.inCb c.inDesc next)) n

/-- An addressed input callback has access to the heap and live pointer cells.
The current Huffman code is a separate local register. -/
theorem need_addressed (strm : ZStreamPtr) (st : InflateStatePtr) (cell : BPtrCell) (input : CInCb)
    (i : VoidPtr) (output : COutCb) (o : VoidPtr) (base : Code) (n : UInt32) :
    KeepsCode base (Zlib.Infback.NEEDBITS (addressedCtx strm st cell input i output o) n) := by
  apply need_ctx
  intro next
  change KeepsCode base (inDecoder _)
  unfold inDecoder
  apply registerFrame_get_bind
  intro regs same
  refine registerFrame_bind (registerFrame_lift _ _) ?_
  rintro ⟨value, cells⟩
  exact registerFrame_bind (registerFrame_set _ _ same) fun _ => registerFrame_pure _ value

theorem drop (base : Code) (n : UInt32) : KeepsCode base (DROPBITS n) := by
  unfold DROPBITS
  register_frame_source

end Zlib.Infback.CodeFrame
