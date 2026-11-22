"""Check header coverage, public contract selection and compiled registry membership."""
import json
from pathlib import Path
import re
import subprocess
import tempfile

from reference import LOCK, ROOT, make_reference


BOUNDARY = "/* undocumented functions (not part of the zlib API) */"
EXPORT = re.compile(r"\bZEXPORT(?:VA)?\s+([A-Za-z_]\w*)\s*\(")


def header_groups(header):
    if header.count(BOUNDARY) != 1:
        raise ValueError("expected one undocumented-functions boundary in zlib.h")

    def declarations(section):
        return set(EXPORT.findall(re.sub(r"/\*.*?\*/", " ", section, flags=re.S)))

    documented, extensions = map(declarations, header.split(BOUNDARY))
    if not documented or not extensions or documented & extensions:
        raise ValueError("ambiguous or empty documented/undocumented sections in zlib.h")
    return documented, extensions


# Inspect elaborated declarations, public entry constructor indices and dispatcher equations.
# The inventory does not supply the code or the names queried by the probe.
REGISTRY_PROBE = """
import Lean
import ZlibF.Results
open Lean Meta Elab Command ZlibF.Results ZlibF.Spec.Public

private def selectedContracts (family : Name) : MetaM (List (String × String)) := do
  (← getConstInfoInduct family).ctors.mapM fun ctor => do
    let ty := (← getConstInfo ctor).type
    let .app (.const result _) (.const goal _) := ty | throwError "expected a contract index at {ctor}"
    unless result == family do throwError "unexpected result type at {ctor}"
    return (ctor.getString!, goal.toString)

run_cmd liftTermElabM do
  let some eqns ← Meta.getEqnsFor? ``Call.execute | throwError "missing equations for Call.execute"
  let dispatch ← eqns.mapM fun eqn => do
    let decl ← getConstInfo eqn
    forallTelescope decl.type fun _ ty => do
      let some (_, lhs, rhs) := ty.eq? | throwError "unexpected equation {eqn}"
      let some call := lhs.getAppArgs[0]? | throwError "missing call in {eqn}"
      let some ctor := call.getAppFn.constName? | throwError "missing constructor in {eqn}"
      let targets := rhs.getUsedConstants.filter fun n => n.getRoot == `Zlib && n.getString! == ctor.getString!
      unless targets.size == 1 do throwError "expected one implementation in {eqn}, found {targets}"
      let impl := targets[0]!
      let env ← getEnv
      let some idx := env.getModuleIdxFor? impl | throwError "no source module for {impl}"
      let path := "/".intercalate (env.header.moduleNames[idx]!.components.map Name.getString!) ++ ".lean"
      return [ctor.getString!, impl.toString, path]
  let entries ← selectedContracts ``PublicEntry
  let protocols ← selectedContracts ``StreamProtocol
  let data := Json.mkObj [
    ("dispatch", toJson dispatch), ("entries", toJson entries), ("protocols", toJson protocols),
    ("proved", toJson (proved.map fun (goal, thm) => (goal.toString, thm.toString))),
    ("required", toJson (required.map Name.toString))]
  IO.println data.compress
"""


def compiled_registry():
    run = subprocess.run(
        ["lake", "env", "lean", "-DwarningAsError=true", "--stdin"],
        cwd=ROOT, input=REGISTRY_PROBE, text=True, stdout=subprocess.PIPE,
    )
    if run.returncode:
        raise RuntimeError(f"Lean registry probe failed\n{run.stdout}")
    return json.loads(run.stdout)


def check_names(context, actual, expected):
    actual = set(actual)
    if actual != expected:
        raise ValueError(f"{context}: missing {sorted(expected - actual)}, unexpected {sorted(actual - expected)}")


def verify(inventory, pin, header, registry):
    if inventory["source_pin"] != pin:
        raise ValueError("inventory source_pin differs from pins.json zlib")
    documented, extensions = header_groups(header)
    indexed = {}
    for row in inventory["apis"]:
        name = row["function"]
        if name in indexed:
            raise ValueError(f"duplicate API inventory entry for {name}")
        indexed[name] = row
    check_names("header versus inventory", indexed, documented | extensions)
    check_names("undocumented functions", inventory["undocumented"]["functions"], extensions)
    entries = dict(registry["entries"])
    check_names("documented header versus PublicEntry constructors", entries, documented)
    dispatch = {name: (impl, source) for name, impl, source in registry["dispatch"]}
    if len(dispatch) != len(registry["dispatch"]):
        raise ValueError("duplicate Call.execute equation for a function")
    proved = dict(registry["proved"])
    required = set(registry["required"])
    sequences = {goal + "_safety" for goal in inventory["sequence_goals"]}
    protocols = {
        "deflate": "ZlibF.Spec.Public.Goal.deflate_sequence_safety",
        "inflate": "ZlibF.Spec.Public.Goal.inflate_sequence_safety",
        "inflateBack": "ZlibF.Spec.Public.Goal.inflate_back_sequence_safety",
        "gzip": "ZlibF.Spec.Public.Goal.gz_sequence_safety",
    }
    check_names("inventory sequence goals", sequences, set(protocols.values()))
    if dict(registry["protocols"]) != protocols:
        raise ValueError(f"StreamProtocol selector mismatch: expected {protocols}, found {registry['protocols']}")
    for goal in sorted(sequences | {"ZlibF.Spec.Public.Goal.whole_library_safety"}):
        if goal not in proved or goal not in required:
            raise ValueError(f"{goal} proved={goal in proved}, required={goal in required}")
    # gzvprintf is below the header's public boundary but has a separately required safety proof.
    contracts = {**entries, "gzvprintf": "ZlibF.Spec.Public.Goal.gzvprintf_safety"}
    if len(set(contracts.values())) != len(contracts):
        raise ValueError("a safety contract is assigned to multiple functions")
    for name, goal in sorted(contracts.items()):
        row = indexed[name]
        if row["scope"] != "lp64-linux":
            raise ValueError(f"{name}: expected default LP64 Linux scope")
        if dispatch.get(name) != (row["implementation"], row["source"]):
            raise ValueError(f"{name}: implementation or source differs from Call.execute {dispatch.get(name)}")
        # Catch a synchronized swap in the inventory and PublicEntry as well as drift between them.
        goal_owner = goal.removeprefix("ZlibF.Spec.Public.Goal.").removesuffix("_safety").removesuffix("_safe")
        if goal_owner != name:
            raise ValueError(f"{name}: public contract {goal} belongs to another function")
        if row["safety_goal"] != goal:
            raise ValueError(f"{name}: expected {goal}, found {row['safety_goal']}")
        if goal not in proved or goal not in required:
            raise ValueError(f"{name}: {goal} proved={goal in proved}, required={goal in required}")
    return len(documented)


def main():
    inventory = json.loads((ROOT / "tests/public-api.json").read_text())
    with tempfile.TemporaryDirectory() as directory:
        ref = Path(directory)
        make_reference(ref)
        header = (ref / "zlib.h").read_text()
    count = verify(inventory, LOCK["zlib"], header, compiled_registry())
    print(f"{count} documented zlib.h functions match compiled dispatch, PublicEntry and required proofs. "
          "gzvprintf also has its required proof.")


if __name__ == "__main__":
    main()
