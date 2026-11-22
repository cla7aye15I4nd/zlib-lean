import Lean.Data.Json

namespace Lean2C.Compare
open System

structure Entry where
  path : String
  status : String
  expectedBytes : Option Nat
  generatedBytes : Option Nat
  firstDifferentByte : Option Nat := none
  deriving Lean.ToJson

private partial def walk (root : FilePath) (rel : FilePath := "") : IO (Array String) := do
  let mut files := #[]
  for file in ← (root / rel).readDir do
    let child : FilePath := if rel.toString.isEmpty then file.fileName else rel / file.fileName
    match (← file.path.symlinkMetadata).type with
    | .dir => files := files ++ (← walk root child)
    | .file => files := files.push child.toString
    | _ => throw <| IO.userError s!"unsupported directory entry: {file.path}"
  return files

private def firstDifference (a b : ByteArray) : Nat := Id.run do
  for i in [:min a.size b.size] do
    if a[i]! != b[i]! then return i
  return min a.size b.size

def compareTrees (expected generated : FilePath) (report : Option FilePath) : IO UInt32 := do
  let left ← walk expected
  let right ← walk generated
  if left.isEmpty then throw <| IO.userError "the expected source tree is empty"
  let names := (left ++ right).toList.eraseDups.toArray.qsort (· < ·)
  let mut entries : Array Entry := #[]
  let mut matched := 0
  let mut matchedBytes := 0
  let mut expectedBytes := 0
  for name in names do
    let a ← if left.contains name then some <$> IO.FS.readBinFile (expected / name) else pure none
    let b ← if right.contains name then some <$> IO.FS.readBinFile (generated / name) else pure none
    let (status, offset) := match a, b with
      | some x, some y => if x == y then ("exact", none) else ("different", some (firstDifference x y))
      | some _, none => ("missing", none)
      | _, _ => ("extra", none)
    let n := a.map ByteArray.size
    expectedBytes := expectedBytes + n.getD 0
    if status == "exact" then
      matched := matched + 1
      matchedBytes := matchedBytes + n.getD 0
    entries := entries.push ⟨name, status, n, b.map ByteArray.size, offset⟩
    let whereAt := offset.map (fun i => s!" at byte {i}") |>.getD ""
    IO.println s!"{status}\t{name}{whereAt}"
  if let some file := report then
    IO.FS.writeFile file ((Lean.toJson entries).pretty ++ "\n")
  IO.println s!"{matched}/{left.size} expected files exact ({matchedBytes}/{expectedBytes} bytes in wholly matching files)."
  return if matched == names.size then 0 else 1

end Lean2C.Compare
