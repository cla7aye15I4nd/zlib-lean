"""Verify 1-to-1 Verus contract coverage against documented zlib.h and exported C ABI."""
import json
import os
from pathlib import Path
import re
import subprocess
import sys

TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))

from reference import BUILD, ROOT, make_reference


ZLIB_H_SPLIT = "/* undocumented functions (not part of the zlib API) */"
DECL_RE = re.compile(r"\bZEXTERN\b[^;]*?\bZEXPORT(?:VA)?\s+([A-Za-z_]\w*)\s*\(", re.S)


def parse_zlib_h():
    zlib_h = BUILD / "reference" / "zlib.h"
    if not zlib_h.exists():
        make_reference(BUILD / "reference")
    text = zlib_h.read_text()
    if ZLIB_H_SPLIT not in text:
        raise ValueError(f"missing marker `{ZLIB_H_SPLIT}` in {zlib_h}")
    doc_part, undoc_part = text.split(ZLIB_H_SPLIT, 1)
    strip_comments = lambda s: re.sub(r"/\*.*?\*/", "", s, flags=re.S)
    doc_apis = set(DECL_RE.findall(strip_comments(doc_part)))
    undoc_apis = set(DECL_RE.findall(strip_comments(undoc_part)))
    posix_undoc = undoc_apis - {"gzopen_w"}
    return doc_apis, posix_undoc


def probe_lean():
    script = """import Zlib.Spec.Safety
open C99
partial def tyCanon : CTy → CTy
  | .const_ t => .const_ (tyCanon t)
  | .ptr t => .ptr (tyCanon t)
  | .array t n => .array (tyCanon t) n
  | .fnPtr r ps v => .fnPtr (tyCanon r) (ps.map tyCanon) v
  | .typedef _ t => tyCanon t
  | t => t
#eval do
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
  let quote := fun (xs : List String) => "[" ++ String.intercalate "," (xs.map (fun s => "\\"" ++ s ++ "\\"")) ++ "]"
  IO.println ("{\\"contracts\\":" ++ quote cNames ++ ",\\"mismatches\\":" ++ quote mismatches ++ ",\\"exports\\":" ++ quote exports ++ "}")
"""
    env = dict(os.environ)
    elan_bin = str(Path.home() / ".elan" / "bin")
    if elan_bin not in env.get("PATH", "").split(os.pathsep):
        env["PATH"] = elan_bin + os.pathsep + env.get("PATH", "")
    proc = subprocess.run(
        ["lake", "env", "lean", "-DwarningAsError=true", "--stdin"],
        cwd=ROOT,
        env=env,
        input=script,
        text=True,
        capture_output=True,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"Lean probe failed:\n{proc.stderr}\n{proc.stdout}")
    for line in proc.stdout.splitlines():
        if line.startswith("{"):
            return json.loads(line)
    raise RuntimeError(f"No JSON payload in Lean probe output:\n{proc.stdout}")


def main():
    doc_apis, posix_undoc = parse_zlib_h()
    expected_exports = doc_apis | posix_undoc
    data = probe_lean()

    contracts = data["contracts"]
    mismatches = data["mismatches"]
    exports = data["exports"]

    dup_contracts = sorted({n for n in contracts if contracts.count(n) > 1})
    dup_exports = sorted({n for n in exports if exports.count(n) > 1})
    if dup_contracts:
        raise AssertionError(f"Duplicate Verus contracts: {dup_contracts}")
    if dup_exports:
        raise AssertionError(f"Duplicate exported symbols in Zlib.allTUs: {dup_exports}")

    contract_set = set(contracts)
    export_set = set(exports)
    missing_contracts = sorted(doc_apis - contract_set)
    extra_contracts = sorted(contract_set - doc_apis)
    if missing_contracts or extra_contracts:
        raise AssertionError(
            f"Contract/zlib.h mismatch: missing={missing_contracts}, extra={extra_contracts}"
        )
    if mismatches:
        raise AssertionError(f"ABI signature mismatches in Zlib.allContracts: {mismatches}")

    missing_exports = sorted(expected_exports - export_set)
    extra_exports = sorted(export_set - expected_exports)
    if missing_exports or extra_exports:
        raise AssertionError(
            f"Export/zlib.h mismatch: missing={missing_exports}, extra={extra_exports}"
        )

    print(
        f"Public API coverage OK: {len(contract_set)}/{len(doc_apis)} Verus contracts in Zlib.allContracts; "
        f"{len(export_set)}/{len(expected_exports)} POSIX exports in Zlib.allTUs; all ABI signatures match."
    )


if __name__ == "__main__":
    main()
