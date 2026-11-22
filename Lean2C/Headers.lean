import ZlibF.Zlib.«crc32.h»
import ZlibF.Zlib.«inffixed.h»
import ZlibF.Zlib.«trees.c»

/-! Source-format emitters for the three generated zlib headers. Table values come
from the definitions used by ZlibF. The printers retain upstream declaration
spellings, comments, and layout. Other CRC configurations are calculated from
the model's byte table, so they do not require a copy of the inactive C tables. -/

namespace Lean2C.Headers

private def rows (items : Array String) (cols : Nat) (sep wrap : String) : String := Id.run do
  let mut out := ""
  for i in [:items.size] do
    if i > 0 then out := out ++ (if i % cols == 0 then wrap else sep)
    out := out ++ items[i]!
  return out

private def pad (c : Char) (width : Nat) (s : String) : String :=
  String.ofList (List.replicate (width - s.length) c) ++ s

private def fixedArray (name : String) (cols : Nat) (data : Array C.Code) : String :=
  let cells := data.map fun v => "{" ++ s!"{v.op},{v.bits},{v.val}" ++ "}"
  "static const code " ++ name ++ "[" ++ toString data.size ++ "] = {\n    " ++
    rows cells cols "," ",\n    " ++ "\n};\n"

def fixed : String :=
  "/* inffixed.h -- table for decoding fixed codes\n * Generated automatically by makefixed().\n */\n\n" ++
  "/* WARNING: this file should *not* be used by applications.\n" ++
  "   It is part of the implementation of this library and is\n" ++
  "   subject to change. Applications should only use zlib.h.\n */\n\n" ++
  fixedArray "lenfix" 7 Zlib.InffixedH.lenfix ++ "\n" ++ fixedArray "distfix" 6 Zlib.InffixedH.distfix

private def treeArray (decl : String) (cols : Nat) (items : Array String) : String :=
  decl ++ " {\n" ++ rows items cols ", " ",\n" ++ "\n};\n\n"

private def pair (w : Nat) (v : C.CtData) : String :=
  "{{" ++ pad ' ' w (toString v.fc) ++ "},{" ++ pad ' ' w (toString v.dl) ++ "}}"

open Zlib.Trees in
def trees : String :=
  "/* header created automatically with -DGEN_TREES_H */\n\n" ++
  treeArray "local const ct_data static_ltree[L_CODES+2] =" 5 (static_ltree_tab.map (pair 3)) ++
  treeArray "local const ct_data static_dtree[D_CODES] =" 5 (static_dtree_tab.map (pair 2)) ++
  treeArray "const uch ZLIB_INTERNAL _dist_code[DIST_CODE_LEN] =" 20
    (dist_code_tab.map fun v => pad ' ' 2 (toString v)) ++
  treeArray "const uch ZLIB_INTERNAL _length_code[MAX_MATCH-MIN_MATCH+1]=" 20
    (length_code_tab.map fun v => pad ' ' 2 (toString v)) ++
  treeArray "local const int base_length[LENGTH_CODES] =" 20 (base_length_tab.map toString) ++
  treeArray "local const int base_dist[D_CODES] =" 10 (base_dist_tab.map fun v => pad ' ' 5 (toString v))

private def swap (w : Nat) (v : UInt32) : UInt64 := Id.run do
  let mut x := v.toUInt64
  let mut out : UInt64 := 0
  for _ in [:w] do
    out := (out <<< 8) ||| (x &&& 255)
    x := x >>> 8
  return out

open Zlib.Crc32H in
private def braid (n w : Nat) : Array (Array UInt32) := Id.run do
  if w == 4 && n == 2 then return crc_braid2_table
  if w == 4 && n == 5 then return crc_braid5_table
  -- Each trailing zero byte advances the reflected CRC by eight powers of x.
  let mut result := #[]
  for k in [:w] do
    let mut row := crc_table
    for _ in [:n * w - k - 1] do
      row := row.map fun (v : UInt32) => (v >>> 8) ^^^ crc_table[(v &&& 255).toNat]!
    result := result.push row
  return result

private def word (w : Nat) (v : UInt64) : String := Id.run do
  let alphabet := "0123456789abcdef".toList.toArray
  let mut digits := []
  let mut n := v
  for _ in [:2 * w] do
    digits := alphabet[(n &&& 15).toNat]! :: digits
    n := n >>> 4
  return "0x" ++ String.ofList digits

private def words (w : Nat) (vs : Array UInt64) : String :=
  rows (vs.map (word w)) (if w == 4 then 5 else 3) ", " ",\n    "

private def flat (decl : String) (w : Nat) (vs : Array UInt64) : String :=
  "local const " ++ decl ++ "[] = {\n    " ++ words w vs ++ "};\n"

private def matrix (decl : String) (w : Nat) (vs : Array (Array UInt64)) : String :=
  "local const " ++ decl ++ "[][256] = {\n" ++
  String.intercalate ",\n" (vs.toList.map fun row => "   {" ++ words w row ++ "}") ++ "};\n"

open Zlib.Crc32H in
private def braidPair (n w : Nat) : String := Id.run do
  let little := braid n w
  let big :=
    if w == 4 && n == 2 then crc_braid2_big_table.map (·.map UInt32.toUInt64)
    else if w == 4 && n == 5 then crc_braid5_big_table.map (·.map UInt32.toUInt64)
    else little.reverse.map (·.map (swap w))
  let name := " FAR crc_braid" ++ toString n
  return matrix ("z_crc_t" ++ name ++ "_table") 4 (little.map (·.map UInt32.toUInt64)) ++ "\n" ++
    matrix ("z_word_t" ++ name ++ "_big_table") w big

open Zlib.Crc32H in
def crc : String := Id.run do
  let mut out := "/* crc32.h -- tables for rapid CRC calculation\n * Generated automatically by crc32.c\n */\n\n"
  out := out ++ flat "z_crc_t FAR crc_table" 4 (crc_table.map UInt32.toUInt64)
  out := out ++ "\n#ifdef W\n\n#if W == 8\n\n" ++ flat "z_word_t FAR crc_big_table" 8 (crc_table.map (swap 8))
  out := out ++ "\n#else /* W == 4 */\n\n" ++ flat "z_word_t FAR crc_big_table" 4 (crc_big_table.map UInt32.toUInt64)
  out := out ++ "\n#endif\n"
  for n in [1:7] do
    out := out ++ s!"\n#if N == {n} || NLOW == {n}\n\n#if W == 8\n\n" ++ braidPair n 8
    out := out ++ "\n#else /* W == 4 */\n\n" ++ braidPair n 4 ++ "\n#endif\n\n#endif\n"
  return out ++ "\n#endif\n\n" ++ flat "z_crc_t FAR x2n_table" 4 (x2n_table.map UInt32.toUInt64)

end Lean2C.Headers
