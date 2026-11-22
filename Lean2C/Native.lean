import Lean2C.Headers

namespace Lean2C.Native
open System

/-- Each implementation and runtime module is an input even if no differential
driver imports it. The backend accepts Lean source and has no C reference input. -/
def emit (out : FilePath) : IO Unit := do
  let root : FilePath := "ZlibF"
  let mut modules : Array (FilePath × FilePath) := #[]
  for group in ["Runtime", "Zlib"] do
    for file in ← (root / group).readDir do
      if file.path.extension != some "lean" then continue
      let stem := file.path.fileStem.get!
      let dest : FilePath :=
        if group == "Runtime" then "support" / "runtime" / (stem ++ ".c")
        else if stem.endsWith ".c" && !stem.startsWith "deflate_" then stem
        else "support" / "model" / (stem ++ ".c")
      modules := modules.push (file.path, dest)
  modules := modules.qsort fun x y => x.1.toString < y.1.toString
  if modules.isEmpty then throw <| IO.userError "missing ZlibF modules; run from the repository root"
  let targets := modules.map fun (path, _) => path.toString ++ ":c"
  let job ← IO.Process.spawn { cmd := "lake", args := #["build", "--wfail"] ++ targets }
  if (← job.wait) != 0 then throw <| IO.userError "Lean C backend failed"
  for (path, dest) in modules do
    let irFile := ((".lake/build/ir" : FilePath) / path).withExtension "c"
    let target := out / dest
    IO.FS.createDirAll target.parent.get!
    IO.FS.writeBinFile target (← IO.FS.readBinFile irFile)
  for (name, data) in [("crc32.h", Headers.crc), ("trees.h", Headers.trees), ("inffixed.h", Headers.fixed)] do
    IO.FS.writeFile (out / name) data
  IO.println s!"Emitted C from {modules.size} Lean modules and three source-format headers to {out}."

end Lean2C.Native
