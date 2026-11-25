import Lean
import C99
import Zlib
import Zlib.Spec.Safety

/-!
# `lean2c` — Unified Zlib-Lean CLI

Provides all Lean-aware C emission, ABI `_Static_assert` generation, `zlib.h` API
coverage verification, and kernel-backed TCB hygiene audits (`emit`, `emit-abi-check`,
`check-api`, `check-tcb`), replacing standalone Python tooling.
-/

open C99

/-! ## 1. Source Emission & ABI `_Static_assert` Generation -/

private def writeAllSources (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  for tu in Zlib.allFiles do
    IO.FS.writeFile (dir / tu.fileName) (EmitC.emitTU tu)

private structure AbiStructSpec where
  tag : String
  refCTy : String
  leanCTy : String

private def deflateAbiStructs : List AbiStructSpec := [
  { tag := "z_stream_s",         refCTy := "struct z_stream_s",  leanCTy := "struct z_stream_s" },
  { tag := "gz_header_s",        refCTy := "struct gz_header_s", leanCTy := "struct gz_header_s" },
  { tag := "ct_data_s",          refCTy := "ct_data",            leanCTy := "struct ct_data_s" },
  { tag := "static_tree_desc_s", refCTy := "static_tree_desc",   leanCTy := "struct static_tree_desc_s" },
  { tag := "tree_desc_s",        refCTy := "tree_desc",          leanCTy := "struct tree_desc_s" },
  { tag := "internal_state",     refCTy := "deflate_state",      leanCTy := "struct internal_state" }
]

private def inflateAbiStructs : List AbiStructSpec := [
  { tag := "code",          refCTy := "code",                 leanCTy := "code" },
  { tag := "inflate_state", refCTy := "struct inflate_state", leanCTy := "struct inflate_state" }
]

private def gzAbiStructs : List AbiStructSpec := [
  { tag := "gzFile_s", refCTy := "struct gzFile_s", leanCTy := "struct gzFile_s" },
  { tag := "gz_state", refCTy := "gz_state",        leanCTy := "gz_state" }
]

private def genStructAsserts (tags : TypeEnv) (spec : AbiStructSpec) (useLeanTy : Bool) :
    Except String (Nat × List String) := do
  let cty := if useLeanTy then spec.leanCTy else spec.refCTy
  let flds ← match tags.lookup spec.tag with
    | some (.structDef fs) => pure fs
    | _ => throw s!"missing struct tag `{spec.tag}` in Zlib.prog.tags"
  let sz := sizeofTy tags (.structTy spec.tag)
  let mut lines := [s!"_Static_assert(sizeof({cty}) == {sz}, \"sizeof mismatch: {spec.tag}\");"]
  for (fname, _) in flds do
    let some (foff, fty) := fieldLayout? tags (.structTy spec.tag) fname
      | throw s!"missing layout for `{spec.tag}.{fname}`"
    let fsz := sizeofTy tags fty
    lines := lines ++ [
      s!"_Static_assert(offsetof({cty}, {fname}) == {foff}, \"offsetof mismatch: {spec.tag}.{fname}\");",
      s!"_Static_assert(sizeof((({cty} *)0)->{fname}) == {fsz}, \"field sizeof mismatch: {spec.tag}.{fname}\");"
    ]
  return (flds.length, lines)

private def renderCheckUnit (tags : TypeEnv) (includes : List String)
    (specs : List AbiStructSpec) (useLeanTy : Bool) : Except String (Nat × String) := do
  let mut lines := includes ++ [""]
  let mut totalFields := 0
  for spec in specs do
    let (nf, ls) ← genStructAsserts tags spec useLeanTy
    totalFields := totalFields + nf
    lines := lines ++ ls
  return (totalFields, String.intercalate "\n" lines ++ "\n")

private def writeAbiChecks (dir : System.FilePath) : IO UInt32 := do
  let tags := Zlib.prog.tags
  let allSpecs := deflateAbiStructs ++ inflateAbiStructs ++ gzAbiStructs
  let checks : List (String × List String × List AbiStructSpec × Bool) := [
    ("abi_check_ref_deflate.c",
      ["#include <stddef.h>", "#include \"zlib.h\"", "#include \"deflate.h\"", "#include \"ref_static_tree_desc.h\""],
      deflateAbiStructs, false),
    ("abi_check_ref_inflate.c",
      ["#include <stddef.h>", "#include \"zutil.h\"", "#include \"inftrees.h\"", "#include \"inflate.h\""],
      inflateAbiStructs, false),
    ("abi_check_ref_gz.c",
      ["#include <stddef.h>", "#include \"gzguts.h\""],
      gzAbiStructs, false),
    ("abi_check_lean.c",
      ["#include <stddef.h>", "#include \"abi_deflate.h\"", "#include \"abi_inflate.h\"", "#include \"abi_gz.h\""],
      allSpecs, true)
  ]
  IO.FS.createDirAll dir
  let mut leanFields := 0
  for (fname, incs, specs, useLean) in checks do
    match renderCheckUnit tags incs specs useLean with
    | .error err =>
      IO.eprintln s!"emit-abi-check error: {err}"
      return 1
    | .ok (nf, src) =>
      if useLean then leanFields := nf
      IO.FS.writeFile (dir / fname) src
  if allSpecs.length != 10 || leanFields != 163 then
    IO.eprintln s!"unexpected ABI count: {allSpecs.length} structs, {leanFields} fields (expected 10, 163)"
    return 1
  IO.println s!"Emitted ABI _Static_assert checks: {allSpecs.length} structs, {leanFields} fields"
  return 0

/-! ## 2. Public API & ABI Signature Verification (`check-api`) -/

private partial def tyCanon : CTy → CTy
  | .const_ t => .const_ (tyCanon t)
  | .ptr t => .ptr (tyCanon t)
  | .array t n => .array (tyCanon t) n
  | .fnPtr r ps v => .fnPtr (tyCanon r) (ps.map tyCanon) v
  | .typedef _ t => tyCanon t
  | t => t

private def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'
private def isIdentChar (c : Char) : Bool := isIdentStart c || c.isDigit
private def isCWhitespace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

private def stripCComments (src : String) : String := Id.run do
  let cs := src.toList.toArray
  let n := cs.size
  let mut out : Array Char := Array.mkEmpty n
  let mut i := 0
  let mut inBlock := false
  while i < n do
    let c := cs[i]!
    let nxt := if i + 1 < n then cs[i + 1]! else '\x00'
    if inBlock then
      if c == '*' && nxt == '/' then
        inBlock := false
        out := out.push ' ' |>.push ' '
        i := i + 2
      else
        out := out.push (if c == '\n' then '\n' else ' ')
        i := i + 1
    else if c == '/' && nxt == '*' then
      inBlock := true
      out := out.push ' ' |>.push ' '
      i := i + 2
    else
      out := out.push c
      i := i + 1
  return String.ofList out.toList

private def matchWordAt (cs : Array Char) (pos : Nat) (word : String) : Bool := Id.run do
  let wcs := word.toList.toArray
  if pos + wcs.size > cs.size then return false
  if pos > 0 && isIdentChar cs[pos - 1]! then return false
  for j in [:wcs.size] do
    if cs[pos + j]! != wcs[j]! then return false
  if pos + wcs.size < cs.size && isIdentChar cs[pos + wcs.size]! then return false
  return true

private def extractZlibExports (src : String) : List String := Id.run do
  let cs := (stripCComments src).toList.toArray
  let n := cs.size
  let mut out : Array String := #[]
  let mut i := 0
  while i < n do
    if matchWordAt cs i "ZEXTERN" then
      let mut j := i + 7
      while j < n && cs[j]! != ';' do
        let zexpLen :=
          if matchWordAt cs j "ZEXPORTVA" then 9
          else if matchWordAt cs j "ZEXPORT" then 7
          else 0
        if zexpLen > 0 then
          let mut k := j + zexpLen
          while k < n && isCWhitespace cs[k]! do
            k := k + 1
          if k < n && isIdentStart cs[k]! then
            let idStart := k
            while k < n && isIdentChar cs[k]! do
              k := k + 1
            let name := String.ofList (cs.extract idStart k).toList
            let mut p := k
            while p < n && isCWhitespace cs[p]! do
              p := p + 1
            if p < n && cs[p]! == '(' then
              out := out.push name
              while j < n && cs[j]! != ';' do
                j := j + 1
              j := j - 1
        j := j + 1
      i := j + 1
    else
      i := i + 1
  return out.toList

private def uniqueSorted (xs : List String) : List String :=
  (xs.toArray.qsort (· < ·)).toList.eraseDups

private def findDuplicates (xs : List String) : List String := Id.run do
  let sorted := (xs.toArray.qsort (· < ·)).toList
  let mut dups : List String := []
  let mut prev? : Option String := none
  for x in sorted do
    if prev? == some x && !dups.contains x then
      dups := dups ++ [x]
    prev? := some x
  return dups

private def runCheckApi (zlibHPath : System.FilePath) : IO UInt32 := do
  let text ← IO.FS.readFile zlibHPath
  let marker := "/* undocumented functions (not part of the zlib API) */"
  let parts := text.splitOn marker
  if parts.length < 2 then
    IO.eprintln s!"missing marker `{marker}` in {zlibHPath}"
    return 1
  let docPart := parts.head!
  let undocPart := String.intercalate marker parts.tail!
  let docApis := uniqueSorted (extractZlibExports docPart)
  let undocApis := uniqueSorted (extractZlibExports undocPart)
  let posixUndoc := undocApis.filter (· != "gzopen_w")
  let expectedExports := uniqueSorted (docApis ++ posixUndoc)

  let cNames := Zlib.allContracts.map (FnContract.fnName (View := Zlib.Spec.ClientView))
  let mismatches := Zlib.allContracts.filterMap fun (c : FnContract Zlib.Spec.ClientView) =>
    match Zlib.prog.fns c.fnName, Zlib.prog.fnProtos c.fnName with
    | some _, some (rt, ps, v) =>
      if tyCanon rt == tyCanon c.retTy && ps.map tyCanon == c.paramTys.map tyCanon && v == c.variadic
      then none else some c.fnName
    | _, _ => some c.fnName
  let exports := (Zlib.allTUs.flatMap TU.items).filterMap fun
    | TopItem.fnDef f => if f.linkage == Linkage.export_ then some f.name else none
    | _ => none

  let dupContracts := findDuplicates cNames
  let dupExports := findDuplicates exports
  if !dupContracts.isEmpty then
    IO.eprintln s!"Duplicate Verus contracts: {dupContracts}"
    return 1
  if !dupExports.isEmpty then
    IO.eprintln s!"Duplicate exported symbols in Zlib.allTUs: {dupExports}"
    return 1

  let contractSet := uniqueSorted cNames
  let exportSet := uniqueSorted exports
  let missingContracts := docApis.filter (!contractSet.contains ·)
  let extraContracts := contractSet.filter (!docApis.contains ·)
  if !missingContracts.isEmpty || !extraContracts.isEmpty then
    IO.eprintln s!"Contract/zlib.h mismatch: missing={missingContracts}, extra={extraContracts}"
    return 1
  if !mismatches.isEmpty then
    IO.eprintln s!"ABI signature mismatches in Zlib.allContracts: {mismatches}"
    return 1

  let missingExports := expectedExports.filter (!exportSet.contains ·)
  let extraExports := exportSet.filter (!expectedExports.contains ·)
  if !missingExports.isEmpty || !extraExports.isEmpty then
    IO.eprintln s!"Export/zlib.h mismatch: missing={missingExports}, extra={extraExports}"
    return 1

  IO.println s!"Public API coverage OK: {contractSet.length}/{docApis.length} Verus contracts in Zlib.allContracts; {exportSet.length}/{expectedExports.length} POSIX exports in Zlib.allTUs; all ABI signatures match."
  return 0

/-! ## 3. Kernel Axiom Check & Source TCB Hygiene Audit (`check-tcb`) -/

private def coreTcbFiles : List String := [
  "C99/AST.lean",
  "C99/Mem.lean",
  "C99/Libc.lean",
  "C99/Semantics.lean",
  "C99/EmitC.lean",
  "C99.lean"
]

private def coreContractFiles : List String := ["C99/DSL/Contract.lean"]
private def specFiles : List String := ["Zlib/Spec/Memory.lean", "Zlib/Spec/Safety.lean"]

private def maxCoreTcbLoc : Nat := 2300
private def maxSpecLoc : Nat := 500

private def forbiddenZlibTokens : List String := [
  "z_stream", "deflate", "inflate", "adler32", "crc32",
  "gzFile", "gz_header", "zlib", "ZLIB", "Z_OK", "Z_STREAM_ERROR"
]

private def coreTcbModules : List Lean.Name := [
  `C99.AST, `C99.Mem, `C99.Libc, `C99.Semantics, `C99.EmitC, `C99, `C99.DSL.Contract
]

private def allowedAxioms : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]

private def countLines (text : String) : Nat :=
  if text.isEmpty then 0
  else
    let lines := text.splitOn "\n"
    if text.endsWith "\n" then lines.length - 1 else lines.length

private def stripLean (stripStrings : Bool) (text : String) : String := Id.run do
  let cs := text.toList.toArray
  let n := cs.size
  let mut out : Array Char := Array.mkEmpty n
  let mut i := 0
  let mut blockDepth : Nat := 0
  let mut inLine := false
  let mut inStr := false
  let mut inChr := false
  while i < n do
    let ch := cs[i]!
    let nxt := if i + 1 < n then cs[i + 1]! else '\x00'
    if inLine then
      if ch == '\n' then
        inLine := false
        out := out.push '\n'
      else
        out := out.push ' '
      i := i + 1
    else if blockDepth > 0 then
      if ch == '/' && nxt == '-' then
        blockDepth := blockDepth + 1
        out := out.push ' ' |>.push ' '
        i := i + 2
      else if ch == '-' && nxt == '/' then
        blockDepth := blockDepth - 1
        out := out.push ' ' |>.push ' '
        i := i + 2
      else
        out := out.push (if ch == '\n' then '\n' else ' ')
        i := i + 1
    else if inStr then
      if stripStrings then
        if ch == '\\' && i + 1 < n then
          out := out.push ' ' |>.push ' '
          i := i + 2
        else if ch == '"' then
          inStr := false
          out := out.push ' '
          i := i + 1
        else
          out := out.push (if ch == '\n' then '\n' else ' ')
          i := i + 1
      else
        if ch == '\\' && i + 1 < n then
          out := out.push ch |>.push nxt
          i := i + 2
        else
          if ch == '"' then inStr := false
          out := out.push ch
          i := i + 1
    else if inChr then
      if ch == '\\' && i + 1 < n then
        out := out.push ' ' |>.push ' '
        i := i + 2
      else if ch == '\'' then
        inChr := false
        out := out.push ' '
        i := i + 1
      else
        out := out.push (if ch == '\n' then '\n' else ' ')
        i := i + 1
    else
      if ch == '-' && nxt == '-' then
        inLine := true
        out := out.push ' ' |>.push ' '
        i := i + 2
      else if ch == '/' && nxt == '-' then
        blockDepth := 1
        out := out.push ' ' |>.push ' '
        i := i + 2
      else if ch == '"' then
        inStr := true
        out := out.push (if stripStrings then ' ' else ch)
        i := i + 1
      else if stripStrings && ch == '\'' && i + 2 < n && (cs[i + 1]! == '\\' || cs[i + 2]! == '\'') then
        inChr := true
        out := out.push ' '
        i := i + 1
      else
        out := out.push ch
        i := i + 1
  return String.ofList out.toList

private def lineHasWord (line word : String) : Bool := Id.run do
  let cs := line.toList.toArray
  for i in [:cs.size] do
    if matchWordAt cs i word then return true
  return false

private def findWordsInText (text : String) (words : List String) : List (Nat × String) := Id.run do
  let mut hits : List (Nat × String) := []
  let mut idx := 1
  for line in text.splitOn "\n" do
    for w in words do
      if lineHasWord line w then
        hits := hits ++ [(idx, w)]
    idx := idx + 1
  return hits

private partial def collectLeanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let entries ← dir.readDir
  let mut acc : Array System.FilePath := #[]
  for e in entries do
    if (← e.path.isDir) then
      acc := acc ++ (← collectLeanFiles e.path)
    else if e.path.extension == some "lean" then
      acc := acc.push e.path
  return acc

private def isLocalModule (m : Lean.Name) : Bool :=
  (`C99).isPrefixOf m || (`Zlib).isPrefixOf m

private partial def transitiveImports (env : Lean.Environment) (roots : List Lean.Name) :
    Except String (List Lean.Name) := do
  let modNames := env.header.moduleNames
  let modData := env.header.moduleData
  let findIdx (m : Lean.Name) : Option Nat := Id.run do
    for i in [:modNames.size] do
      if modNames[i]! == m then return some i
    return none
  let mut queue := roots
  let mut visited : Lean.NameSet := {}
  while !queue.isEmpty do
    let m := queue.head!
    queue := queue.tail!
    if visited.contains m then continue
    visited := visited.insert m
    let some idx := findIdx m
      | throw s!"module `{m}` missing from loaded Lean environment"
    for imp in modData[idx]!.imports do
      if !visited.contains imp.module then
        queue := queue ++ [imp.module]
  return visited.toList

private def checkKernelEnv : IO (Option String) := do
  Lean.initSearchPath (← Lean.findSysroot) [System.FilePath.mk ".lake/build/lib/lean"]
  let env ← Lean.importModules #[{ module := `Zlib.Spec.Safety }] {}
  match transitiveImports env coreTcbModules with
  | .error e => return some e
  | .ok deps =>
    let zlibDeps := deps.filter ((`Zlib).isPrefixOf ·)
    if !zlibDeps.isEmpty then
      return some s!"Core TCB modules transitively import Zlib modules: {zlibDeps}"

  let modNames := env.header.moduleNames
  let mut targets : Array Lean.Name := #[``Zlib.Spec.Goal.libz_safety]
  for (cname, _) in env.constants do
    if let some idx := env.getModuleIdxFor? cname then
      if isLocalModule modNames[idx]! then
        targets := targets.push cname

  let ctx : Lean.Core.Context := { fileName := "<check-tcb>", fileMap := Inhabited.default }
  let (bad?, _) ← (Lean.Core.CoreM.toIO (ctx := ctx) (s := { env := env }) do
    for cname in targets do
      let axs ← Lean.collectAxioms cname
      let bad := axs.filter (!allowedAxioms.contains ·)
      if !bad.isEmpty then
        return some s!"disallowed axioms in `{cname}`: {bad.toList}"
    return none)
  return bad?

private def runCheckTcb : IO UInt32 := do
  if let some err ← checkKernelEnv then
    IO.eprintln s!"Kernel check failed: {err}"
    return 1

  let mut files : Array System.FilePath := #[]
  for folder in ["C99", "Zlib"] do
    files := files ++ (← collectLeanFiles ⟨folder⟩)
  files := (files.qsort (·.toString < ·.toString)).push ⟨"Zlib.lean"⟩ |>.push ⟨"Main.lean"⟩

  let mut sorryHits : List String := []
  let mut axiomHits : List String := []
  for p in files do
    let text ← IO.FS.readFile p
    let stripped := stripLean true text
    for (ln, w) in findWordsInText stripped ["sorry", "axiom"] do
      if w == "sorry" then sorryHits := sorryHits ++ [s!"{p}:{ln}"]
      else axiomHits := axiomHits ++ [s!"{p}:{ln}"]
  if !sorryHits.isEmpty then
    IO.eprintln s!"Found `sorry` in: {sorryHits}"
    return 1
  if !axiomHits.isEmpty then
    IO.eprintln s!"Found `axiom` in: {axiomHits}"
    return 1

  let mut zlibLeaks : List String := []
  for rel in coreTcbFiles ++ coreContractFiles do
    let text ← IO.FS.readFile ⟨rel⟩
    let stripped := stripLean false text
    for (ln, tok) in findWordsInText stripped forbiddenZlibTokens do
      zlibLeaks := zlibLeaks ++ [s!"{rel}:{ln} ({tok})"]
  if !zlibLeaks.isEmpty then
    IO.eprintln s!"Found zlib-specific identifier in Core TCB: {zlibLeaks}"
    return 1

  let countList (rels : List String) : IO Nat :=
    rels.foldlM (fun acc rel => do return acc + countLines (← IO.FS.readFile ⟨rel⟩)) 0
  let coreLoc ← countList coreTcbFiles
  let contractLoc ← countList coreContractFiles
  let specLoc ← countList specFiles

  let dslFiles := (← collectLeanFiles ⟨"C99/DSL"⟩).toList.filter fun p => p.toString != "C99/DSL/Contract.lean"
  let dslLoc ← dslFiles.foldlM (fun acc p => do return acc + countLines (← IO.FS.readFile p)) 0
  let zlibFiles := (← collectLeanFiles ⟨"Zlib"⟩).toList.filter fun p => !(p.toString.startsWith "Zlib/Spec/")
  let zlibTusLoc ← zlibFiles.foldlM (fun acc p => do return acc + countLines (← IO.FS.readFile p)) 0

  if coreLoc > maxCoreTcbLoc then
    IO.eprintln s!"Core TCB LOC {coreLoc} exceeds budget {maxCoreTcbLoc}"
    return 1
  if specLoc > maxSpecLoc then
    IO.eprintln s!"Zlib/Spec LOC {specLoc} exceeds budget {maxSpecLoc}"
    return 1

  IO.println "TCB & Cleanliness Audit Summary:"
  IO.println s!"  Core C99 TCB (AST, Mem, Libc, Semantics, EmitC, C99): {coreLoc} LOC (limit {maxCoreTcbLoc})"
  IO.println s!"  Verus Contract Interface (C99/DSL/Contract):          {contractLoc} LOC"
  IO.println s!"  C-like DSL Frontend (C99/DSL/*):                      {dslLoc} LOC"
  IO.println s!"  Safety-Only Spec (Zlib/Spec/*):                       {specLoc} LOC (limit {maxSpecLoc})"
  IO.println s!"  Zlib C-like Translation Units + Headers + Tables:     {zlibTusLoc} LOC"
  IO.println "  Cleanliness: 0 sorry, 0 axiom, 0 zlib identifiers in Core TCB (kernel + source verified)."
  return 0

/-! ## 4. Entrypoint -/

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] | ["abi-sources", dir] =>
    writeAllSources ⟨dir⟩
    return 0
  | ["emit-abi-check", dir] =>
    writeAbiChecks ⟨dir⟩
  | ["check-api", zlibH] =>
    runCheckApi ⟨zlibH⟩
  | ["check-tcb"] =>
    runCheckTcb
  | _ =>
    IO.eprintln "usage: lean2c (emit|emit-abi-check) <dir> | lean2c check-api <zlib.h> | lean2c check-tcb"
    return 1
