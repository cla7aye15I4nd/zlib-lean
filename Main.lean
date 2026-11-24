import C99
import Zlib

open C99

private def writeAllSources (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  for tu in Zlib.allFiles do
    IO.FS.writeFile (dir / tu.fileName) (EmitC.emitTU tu)

private def jsonEscape (s : String) : String :=
  s.foldl (fun acc c => match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | _ => acc.push c) ""

private def renderLayoutJson : String :=
  let tags := Zlib.prog.tags
  let entries := tags.filterMap fun (tag, defn) =>
    match defn with
    | .structDef flds | .unionDef flds =>
      let cty := match defn with | .structDef _ => CTy.structTy tag | _ => CTy.unionTy tag
      let sz := sizeofTy tags cty
      let al := alignofTy tags cty
      let fJson := flds.filterMap fun (fn, _) =>
        (fieldLayout? tags cty fn).map fun (off, fty) =>
          let fsz := sizeofTy tags fty
          s!"\"{jsonEscape fn}\": \{\"offset\": {off}, \"size\": {fsz}}"
      some s!"  \"{jsonEscape tag}\": \{\"size\": {sz}, \"align\": {al}, \"fields\": \{{String.intercalate ", " fJson}}}"
    | .enumDef _ _ => none
  "{\n" ++ String.intercalate ",\n" entries ++ "\n}"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["abi-sources", dir] | ["emit", dir] =>
    writeAllSources ⟨dir⟩
    return 0
  | ["layout-json"] =>
    IO.println renderLayoutJson
    return 0
  | _ =>
    IO.eprintln "usage: lean2c (abi-sources|emit) <dir> | lean2c layout-json"
    return 1
