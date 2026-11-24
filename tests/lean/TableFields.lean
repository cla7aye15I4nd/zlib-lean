import Lean2C.Simple
import ZlibF.Zlib.«inflate.c»
import ZlibF.Zlib.«adler32.c»
open C Zlib.Inflate Zlib.Inftrees
namespace TableFields

def forward (st : InflateStatePtr) : M (CExport Int32) := do
  let s ← ldInflateState st
  let (rc, nx, bits) ← inflate_table CODES (lensP st) 19 s.next s.lenbits (workP st)
  wrS st fun current => { current with next := nx, lenbits := bits }
  return rc

def other_state (st : InflateStatePtr) (other : InflateStatePtr) : M (CExport Int32) := do
  let s ← ldInflateState st
  let (rc, nx, bits) ← inflate_table CODES (lensP st) 19 s.next s.lenbits (workP st)
  wrS other fun current => { current with next := nx, lenbits := bits }
  return rc

def other_bits (st : InflateStatePtr) : M (CExport Int32) := do
  let s ← ldInflateState st
  let (rc, nx, bits) ← inflate_table CODES (lensP st) 19 s.next s.lenbits (workP st)
  wrS st fun current => { current with next := nx, distbits := bits }
  return rc

def changed_bits (st : InflateStatePtr) : M (CExport Int32) := do
  let s ← ldInflateState st
  let (rc, nx, bits) ← inflate_table CODES (lensP st) 19 s.next (s.lenbits + 1) (workP st)
  wrS st fun current => { current with next := nx, lenbits := bits }
  return rc

def discard (st : InflateStatePtr) : M (CExport Int32) := do
  let s ← ldInflateState st
  let (rc, _, _) ← inflate_table CODES (lensP st) 19 s.next s.lenbits (workP st)
  return rc

def intervening_write (st : InflateStatePtr) : M (CExport Int32) := do
  let s ← ldInflateState st
  wrS st fun current => { current with lenbits := 9 }
  let (rc, nx, bits) ← inflate_table CODES (lensP st) 19 s.next s.lenbits (workP st)
  wrS st fun current => { current with next := nx, lenbits := bits }
  return rc

def delayed_result (st : InflateStatePtr) : M (CExport UInt32) := do
  let s ← ldInflateState st
  let (_, nx, bits) ← inflate_table CODES (lensP st) 19 s.next s.lenbits (workP st)
  wrS st fun current => { current with next := nx, lenbits := bits }
  wrS st fun current => { current with lenbits := 23 }
  return bits

def delayed_commit (st : InflateStatePtr) : M (CExport Int32) := do
  let s ← ldInflateState st
  let (rc, nx, bits) ← inflate_table CODES (lensP st) 19 s.next s.lenbits (workP st)
  wrS st fun current => { current with distbits := 23 }
  wrS st fun current => { current with next := nx, lenbits := bits }
  return rc

def extra_update (st : InflateStatePtr) : M (CExport Int32) := do
  let s ← ldInflateState st
  let (rc, nx, bits) ← inflate_table CODES (lensP st) 19 s.next s.lenbits (workP st)
  wrS st fun current => { current with next := nx, lenbits := bits, distbits := 23 }
  return rc

def aliased_update (st other : InflateStatePtr) : M (CExport UInt32) := do
  let s ← ldInflateState st
  wrS other fun current => { current with lenbits := 23 }
  return s.lenbits

def swap_widths (st : InflateStatePtr) : M (CExport Unit) := do
  wrS st fun s => { s with lenbits := s.distbits, distbits := s.lenbits }

def chained_widths (st : InflateStatePtr) : M (CExport Unit) :=
  wrS st fun initial =>
    let step := { initial with distbits := initial.lenbits + 1 }
    let next := { step with lenbits := step.distbits + 2 }
    { next with distbits := next.lenbits + initial.distbits }

def optional_count (n : UInt32) : M (CExport UInt32) := do
  let v ← cdecl (if n == 0 then (none : Option UInt32) else some (n - 1))
  if let some count := v then return count
  return 77

def nested_range (limit : UInt32) : M (CExport UInt32) := do
  let mut count : UInt32 := 0
  for _ in [0:3] do
    for i in [0:5] do
      if i == limit.toNat then break
      count := count + 1
  return count

def helper_locals (buf : BPtr) (adler : UInt64) : M (CExport UInt64) := do
  let initial : Zlib.Adler32.Locals := ⟨1, 0, buf, 1, 0⟩
  let updated ← Zlib.Adler32.do1 initial 0
  return adler + updated.adler

end TableFields

open Lean Elab Term
private def layout (s : Syntax) : TermElabM String := do
  let .lit (.strVal v) ← elabTerm s (some (mkConst ``String)) | throwError "invalid layout"
  return v
elab "tableFieldsSource%" : term => do
  let zs ← layout (← `(abiZStream%))
  let inf ← layout (← `(abiInflateLayouts%))
  let defl ← layout (← `(abiDeflateLayouts%))
  let gz ← layout (← `(abiGzLayouts%))
  return toExpr (← Lean2C.Simple.compileModule `TableFields zs inf defl gz)
