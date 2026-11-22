import ZlibF.Zlib.«deflate_base.c»
import ZlibF.Proof.«deflate.c.engine.macros»
import ZlibF.Proof.«deflate.c.engine.loops»
import ZlibF.Proof.«adler32.c»
import ZlibF.Proof.«crc32.c»

/-!
# deflate.c, engine: `read_buf`

`read_buf(strm, buf, size)` copies `L = min(avail_in, size)` bytes from `next_in` to `buf`, advances `next_in`,
`total_in`, lowers `avail_in`, and updates `adler` with the Adler-32 (`wrap = 1`) or CRC-32 (`wrap = 2`) of the bytes
copied. Nothing else changes. The checksum theorems of `adler32.c` and `crc32.c` are used as proved.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate

/-- `len = strm->avail_in; if (len > size) len = size;` -/
def rbLen (avail size : UInt32) : UInt32 := if avail > size then size else avail

theorem seg_eq_take_drop (a : Array UInt8) (p n : Nat) (h : p + n ≤ a.size) :
    Zlib.Adler32.Proofs.seg a p n = (a.toList.drop p).take n := by
  apply List.ext_getElem
  · simp [Zlib.Adler32.Proofs.seg]; omega
  · intro i h1 h2
    simp [Zlib.Adler32.Proofs.seg] at h1 ⊢
    simp [getElem!_def, Array.getElem?_eq_getElem (show p + i < a.size by omega)]

theorem seg_copyRange (ba ia : Array UInt8) (bo io L : Nat) (hfit : bo + L ≤ ba.size) :
    Zlib.Adler32.Proofs.seg (copyRange ba ia bo io L) bo L = Zlib.Adler32.Proofs.seg ia io L := by
  unfold Zlib.Adler32.Proofs.seg
  apply List.map_congr_left
  intro i hi
  have hi' : i < L := List.mem_range.mp hi
  have := getElem?_copyRange ba ia bo io L (bo + i) hfit
  simp only [getElem!_def, this, show bo ≤ bo + i ∧ bo + i < bo + L by omega, and_self, ite_true,
    Nat.add_sub_cancel_left]

/-- `strm->avail_in -= len` -/
def rbDec (L : UInt32) : ZStream → ZStream := fun z => { z with avail_in := z.avail_in - L }
/-- `strm->adler = a` -/
def rbSetAd (a : UInt64) : ZStream → ZStream := fun z => { z with adler := a }
/-- `strm->next_in += len; strm->total_in += len` (the new `next_in` is `ni`) -/
def rbAdvF (ni : BPtr) (L : UInt32) : ZStream → ZStream := fun z => { z with next_in := ni, total_in := z.total_in + L.toUInt64 }

/-- `read_buf` with the length already computed (`len` is `min(avail_in, size)`). -/
def rbCore (strm : ZStreamPtr) (buf : BPtr) (len : UInt32) : M UInt32 := do
  if len == 0 then return 0
  zwr strm (rbDec len)
  memcpyB buf (← zrd strm (·.next_in)) len.toNat
  let sp ← castDeflateState (← zrd strm (·.state))
  let wrap ← rd sp (·.wrap)
  if wrap == 1 then
    let a ← zrd strm (·.adler)
    let r ← Zlib.Adler32.adler32 a buf len
    zwr strm (rbSetAd r)
  else if wrap == 2 then
    let a ← zrd strm (·.adler)
    let r ← Zlib.Crc32.crc32 a buf len
    zwr strm (rbSetAd r)
  let ni ← padd (← zrd strm (·.next_in)) len.toNat
  zwr strm (rbAdvF ni len)
  return len

end Zlib.Deflate.Engine.Proofs
