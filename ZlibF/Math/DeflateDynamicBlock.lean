import ZlibF.Proof.«trees.c.dynamic-header»

/-! # Actual dynamic tags and the independent block-sequence grammar -/

namespace Zlib.Trees.Proofs
open C ZlibF.Spec Out
set_option autoImplicit false

theorem dynamicTag_wire (last : Bool) :
    dynamicTag last = natBits (if last then 1 else 0) 1 ++ natBits 2 2 := by
  cases last <;> decide +kernel

end Zlib.Trees.Proofs
