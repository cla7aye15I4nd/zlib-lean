import Lean2C.Macros
import Lean2C.Forward
import Lean2C.Compare
import Lean2C.Native
import Lean2C.Archive

private def usage : String :=
  "usage: lean2c emit DIRECTORY | abi-sources DIRECTORY | function LEAN_NAME | symbols FILE.json | macros FILE.json | bodies FILE.json | candidates FILE.json | compare EXPECTED GENERATED [REPORT.json]"

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["function", name] =>
      let some (_, body) := Lean2C.Forward.bodies.find? (·.1 == name)
        | IO.eprintln s!"No source-form lowering for {name}"; return 1
      IO.println body
      return 0
    | ["symbols", out] =>
      IO.FS.writeFile out ((Lean.toJson Lean2C.Forward.symbols).pretty ++ "\n")
      return 0
    | ["macros", out] =>
      IO.FS.writeFile out ((Lean.toJson Lean2C.macros).pretty ++ "\n")
      return 0
    | ["bodies", out] =>
      IO.FS.writeFile out ((Lean.toJson Lean2C.Forward.bodies).pretty ++ "\n")
      return 0
    | ["candidates", out] =>
      IO.FS.writeFile out ((Lean.toJson Lean2C.Forward.candidates).pretty ++ "\n")
      return 0
    | ["abi-sources", out] => Lean2C.Archive.emit out; return 0
    | ["emit", out] => Lean2C.Native.emit out; return 0
    | ["compare", a, b] => Lean2C.Compare.compareTrees a b none
    | ["compare", a, b, report] => Lean2C.Compare.compareTrees a b (some report)
    | _ => IO.eprintln usage; return 2
  catch e =>
    IO.eprintln (toString e)
    return 2
