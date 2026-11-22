import ZlibF.Zlib.«inffast.c»
import ZlibF.Spec.Common.Inflate.FastTable
import ZlibF.Spec.Common.InflateGood
import ZlibF.Spec.Common.Bits
import ZlibF.Spec.Common.Inflate.WindowCopy

/-!
# inffast.c: the situation of `inflate_fast`

`EnvG` bundles what `inflate_fast` needs of the heap at entry with the witnesses (byte views, offsets, arrays).
`LS` relates the locals to it, `Sg` is the bit sequence that the bit buffer and the unread input stand for, and
`CtxOK` says that the context the function builds is the one `EnvG` describes. The lemmas about them are in the
proof modules `ZlibF/Proof/inffast.c.*.lean`.
-/

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec

/-- How the window block relates to the output view. Without `alias` (every `Env`): another
view. With `alias` (`inflateBack`, whose output is the window): the output view itself is
allowed, and then `wnext = 0` and the window ends no later than the output range (`inside`). -/
@[reducible] def WinRel : Bool → Nat → BRef → UInt32 → Prop → Prop
  | false, wb, ob, _, _ => BRef.blk wb ≠ ob
  | true, wb, ob, wnext, inside => BRef.blk wb = ob → wnext = 0 ∧ inside

/-- Everything `inflate_fast` needs of the heap `h0` at entry, with the witnesses. These are the preconditions of
`inflate_fast_safe` (`Zlib.Inffast.Proofs.Env.of_pre` builds one from the hypotheses of the theorem). -/
structure EnvG (alias : Bool) where
  h0 : Heap
  strm : ZStreamPtr
  start : UInt32
  -- the stream record and the state
  r : ZStreamRef
  sm0 : ZStream
  stid : Nat
  s0 : InflateState
  hstrm : strm = some r
  hsm : r.get h0 = some sm0
  hrw : r.isRo = false
  hstate : sm0.state = some (StateRef.inflate stid)
  hs0 : h0.istates stid = some s0
  -- the input
  ib : BRef
  i0 : Nat
  IN : Array UInt8
  hnin : sm0.next_in = .ref ib i0
  hIN : Space.get h0 ib = some IN
  hai : 6 ≤ sm0.avail_in.toNat
  hINsz : i0 + sm0.avail_in.toNat ≤ IN.size
  hINbig : IN.size < 2 ^ 63
  -- the output
  ob : BRef
  o0 : Nat
  A0 : Array UInt8
  hnout : sm0.next_out = .ref ob o0
  hA0 : Space.get h0 ob = some A0
  hro : Space.ro h0 ob = false
  hao : 258 ≤ sm0.avail_out.toNat
  hAsz : o0 + sm0.avail_out.toNat ≤ A0.size
  hAbig : A0.size < 2 ^ 63
  hstart : sm0.avail_out.toNat ≤ start.toNat
  hbeg : start.toNat - sm0.avail_out.toNat ≤ o0
  /-- Input and output are distinct byte views, or disjoint ranges of one view. -/
  hsep : ib ≠ ob ∨ (ib = ob ∧
    (i0 + sm0.avail_in.toNat ≤ o0 ∨ o0 + sm0.avail_out.toNat ≤ i0))
  -- the bit buffer
  hbits : s0.bits.toNat < 8
  hhold : s0.hold.toNat < 2 ^ s0.bits.toNat
  hsane : s0.sane ≠ 0
  hmode : s0.mode = LEN
  halias_win : alias = true → s0.window ≠ .null
  -- the window
  hws : s0.wsize.toNat ≤ 32768
  hwh : s0.whave.toNat ≤ s0.wsize.toNat
  hwn : s0.wnext.toNat ≤ s0.wsize.toNat
  wb : Nat
  woff : Nat
  W : Array UInt8
  hwin : s0.whave ≠ 0 →
    s0.window = .ref (BRef.blk wb) woff ∧
      WinRel alias wb ob s0.wnext (woff + s0.wsize.toNat ≤ o0 + sm0.avail_out.toNat) ∧ h0.bytes wb = some W ∧
      woff + s0.wsize.toNat ≤ W.size
  hwinLive : s0.window ≠ .null →
    s0.window = .ref (BRef.blk wb) woff ∧
      (match alias with
       | false => BRef.blk wb ≠ ob
       | true => BRef.blk wb = ob ∧ s0.wnext = 0 ∧ woff + s0.wsize.toNat = o0 + sm0.avail_out.toNat) ∧
      h0.bytes wb = some W ∧ woff + s0.wsize.toNat ≤ W.size
  -- the tables
  rl : CodeRef
  ol : Nat
  LCA : Array Code
  hlc : s0.lencode = .ref rl ol
  hLCA : Space.get h0 rl = some LCA
  hlt : LenTableSafe LCA ol s0.lenbits.toNat
  rd : CodeRef
  od : Nat
  DCA : Array Code
  hdc : s0.distcode = .ref rd od
  hDCA : Space.get h0 rd = some DCA
  hdt : DistTableSafe DCA od s0.distbits.toNat

/-- The situation of every caller but `inflateBack`: the window is another block than the output. -/
abbrev Env := EnvG false

/-- The heap while `inflate_fast` runs: the output view is `A`, the message of the stream is `msg` and the mode of
the state is `m`; nothing else differs from `h0`. -/
def EnvG.heap {α : Bool} (e : EnvG α) (A : Array UInt8) (msg : BPtr) (m : UInt32) : Heap :=
  ZStreamRef.put
    (Space.put (Zlib.Inflate.Spec.setI e.h0 e.stid { e.s0 with mode := m }) e.ob A)
    e.r { e.sm0 with msg := msg }

section
variable {α : Bool} (e : EnvG α)

/-- When input and output share a block, the output array `A` has the size of
the block at entry and agrees with the input at entry from `i` to the end of
the input. -/
def EnvG.InputFrame (A : Array UInt8) (i : Nat) : Prop :=
  e.ib = e.ob → A.size = e.A0.size ∧
    ∀ k, i ≤ k → k < e.i0 + e.sm0.avail_in.toNat → A[k]? = e.IN[k]?

/-- The locals are consistent with the situation: `in` is at offset `i` of the input block, `out` at offset `o` of the
output block, both within their windows; the bit buffer holds `bits ≤ 30` bits; and the bits read so far account for
the bytes consumed (`bits ≤ bits_at_entry + 8 * (i - i0)`). -/
structure LS (l : L) (i o : Nat) : Prop where
  hin : l.in_ = .ref e.ib i
  hout : l.out = .ref e.ob o
  hi0 : e.i0 ≤ i
  hi1 : i ≤ e.i0 + e.sm0.avail_in.toNat
  ho0 : e.o0 ≤ o
  hb : l.bits.toNat ≤ 30
  hH : l.hold.toNat < 2 ^ l.bits.toNat
  hacc : l.bits.toNat + 8 * e.i0 ≤ e.s0.bits.toNat + 8 * i

end

open ZlibF.Spec

/-- The low `b` bits of `H`, least significant first. -/
def bitsOfNat (H b : Nat) : List Bool := (List.range b).map fun j => H.testBit j

section
variable {α : Bool} (e : EnvG α)

/-- The bits of the input bytes from offset `i` to the end of the input range. -/
def inBits (i : Nat) : List Bool :=
  bytesToBits ((e.IN.toList.drop i).take (e.i0 + e.sm0.avail_in.toNat - i))

/-- The bit sequence of a state: the bits of the buffer, then the bits of the unread input. -/
def Sg (H b i : Nat) : List Bool := bitsOfNat H b ++ inBits e i

end

/-- `hold >>= k; bits -= k;` -/
def dropL (l : L) (k : UInt32) : L := { l with hold := l.hold >>> k.toUInt64, bits := l.bits - k }

/-- The offset of `beg` in the output block: `next_out - (start - avail_out)`. -/
def EnvG.bg {α : Bool} (e : EnvG α) : Nat := e.o0 - (e.start.toNat - e.sm0.avail_out.toNat)

/-- The context `c` that `inflate_fast` builds is the one the situation `e` describes. -/
structure CtxOK {α : Bool} (e : EnvG α) (c : Ctx) : Prop where
  strm : c.strm = e.strm
  state : c.state = some (InflateStateRef.tab e.stid)
  last : c.last = .ref e.ib (e.i0 + e.sm0.avail_in.toNat - 5)
  beg : c.beg = .ref e.ob e.bg
  end_ : c.end_ = .ref e.ob (e.o0 + e.sm0.avail_out.toNat - 257)
  wsize : c.wsize = e.s0.wsize
  whave : c.whave = e.s0.whave
  wnext : c.wnext = e.s0.wnext
  window : c.window = e.s0.window
  lcode : c.lcode = e.s0.lencode
  dcode : c.dcode = e.s0.distcode
  lmask : c.lmask = ((1 : UInt32) <<< e.s0.lenbits) - 1
  dmask : c.dmask = ((1 : UInt32) <<< e.s0.distbits) - 1

/-- The entry on which a distance lookup ends and the number of bits it consumes, for the hold value `H` and the root
index `kidx`: a root leaf, or a root link and a leaf of its second level. -/
def DistLook {α : Bool} (e : EnvG α) (H kidx : Nat) (E : Code) (cb : Nat) : Prop :=
  (e.DCA.getD (e.od + kidx) default = E ∧ cb = E.bits.toNat ∧ ¬ DistLink E) ∨
  (∃ E0 j, e.DCA.getD (e.od + kidx) default = E0 ∧ DistLink E0 ∧ j < 2 ^ E0.op.toNat ∧
     j = (H / 2 ^ E0.bits.toNat) % 2 ^ E0.op.toNat ∧ e.DCA.getD (e.od + E0.val.toNat + j) default = E ∧
     cb = E0.bits.toNat + E.bits.toNat ∧ E0.bits.toNat + E.bits.toNat ≤ 15 ∧ ¬ DistLink E)

/-- The match result of the situation: `matchArr` over the window array, or `matchArrA` when the
window is the output block. -/
def EnvG.mArr : {α : Bool} → EnvG α → Nat → Nat → Nat → Nat → Array UInt8 → Array UInt8
  | false, e, bg, o, dist, len, A => matchArr e.s0.wsize.toNat e.s0.wnext.toNat e.woff e.W bg o dist len A
  | true, e, bg, o, dist, len, A =>
    if BRef.blk e.wb = e.ob then matchArrA e.s0.wsize.toNat e.woff bg o dist len A
    else matchArr e.s0.wsize.toNat e.s0.wnext.toNat e.woff e.W bg o dist len A

/-- `dodist:` reached from the length block: look up the distance code and run the distance block. -/
def dolenDist (c : Ctx) (l : L) : M L := do
  let __do_lift ← Ptr.add c.dcode ↑(l.hold &&& c.dmask.toUInt64).toNat
  let l : L := { l with here := __do_lift }
  cdoWhile (dodist c) (fun l => pure (l.againD, l)) l

/-- `l` after `hold += (unsigned long)(*in++) << bits; bits += 8;` with the byte `x` and the new pointer `p`. -/
def pullL (l : L) (x : UInt8) (p : BPtr) : L :=
  { l with in_ := p, hold := l.hold + (x.toUInt64 <<< l.bits.toUInt64), bits := l.bits + 8 }

end Zlib.Inffast.Proofs
