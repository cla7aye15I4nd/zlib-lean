import ZlibF.Proof.«deflate.c.engine.public-header»

/-! # Actual zlib-header execution with the compression level retained -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

/-- The level flags are computed by the translated standard-strategy header. -/
def levelHeaderFlags (level : Int32) : UInt32 :=
  if level < 2 then 0 else if level < 6 then 1 else if level == 6 then 2 else 3

/-- Actual header arithmetic at windowBits fifteen, without a dictionary. -/
def levelHeaderWord (level : Int32) : UInt32 :=
  let raw := (((8 : UInt32) + (((15 : UInt32) - 8) <<< 4)) <<< 8) ||| (levelHeaderFlags level <<< 6)
  raw + ((31 : UInt32) - raw % 31)

def levelHeaderBytes (level : Int32) (buf : Array UInt8) : Array UInt8 :=
  (buf.set! 0 ((levelHeaderWord level >>> 8).toUInt8)).set! 1 ((levelHeaderWord level &&& 0xff).toUInt8)

def levelHeaderState (d : DeflateState) : DeflateState :=
  { d with pending := 2, status := BUSY_STATE }

def levelHeaderReady (h : Heap) (r : ZStreamRef) (ds pb : Nat)
    (z : ZStream) (d : DeflateState) (buf : Array UInt8) : Heap :=
  setD (r.put { h with bytes := upd h.bytes pb (some (levelHeaderBytes d.level buf)) } { z with adler := 1 }) ds
    (levelHeaderState d)

end Zlib.Deflate.Engine.Proofs
