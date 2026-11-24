"""Check the two LP64 size-bound proofs against both sources used by the archive build."""
import json
from pathlib import Path
import re
import subprocess
import tempfile

from archive import prepare_inputs
from ast_compare import clang, function_body, location, objects
from reference import ROOT


NAMES = ("compressBound_z", "compressBound")
TYPES = {"unsigned long": ".u64", "int": ".i32"}
SIGNATURES = {
    "compressBound_z": {"z_size_t (z_size_t)", "unsigned long (unsigned long)"},
    "compressBound": {"uLong (uLong)", "unsigned long (unsigned long)"},
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def ctype(node):
    t = node["type"]
    name = t.get("desugaredQualType", t["qualType"])
    require(name in TYPES, f"unsupported scalar type {name}")
    return TYPES[name]


def local_name(node):
    name = node["name"]
    require(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", name), f"invalid identifier {name!r}")
    return json.dumps(name)


def expr(node, scope, callee_id):
    kind = node["kind"]
    args = node.get("inner", [])
    t = ctype(node)

    def read(child):
        return expr(child, scope, callee_id)

    if kind == "DeclRefExpr":
        ref = node["referencedDecl"]
        require(not args and ref["kind"] in {"ParmVarDecl", "VarDecl"} and
                scope.get(ref["id"]) == (local_name(ref), t) and ctype(ref) == t, "unbound scalar read")
        return f"(.var {t} {local_name(ref)})"
    if kind == "IntegerLiteral":
        value = int(node["value"])
        require(not args and 0 <= value < (1 << (31 if t == ".i32" else 64)), "invalid integer literal")
        return f"(.num {t} {value})"
    if kind == "BinaryOperator":
        a, b = args
        op = node["opcode"]
        valid = ((op == "+" and ctype(a) == ctype(b) == t == ".u64") or
                 (op == ">>" and ctype(a) == t == ".u64" and ctype(b) in {".u64", ".i32"}) or
                 (op in {"<", "!="} and ctype(a) == ctype(b) == ".u64" and t == ".i32"))
        require(valid, f"unsupported arithmetic or conversion in {op}")
        return f"(.op {t} {json.dumps(op)} {read(a)} {read(b)})"
    if kind == "UnaryOperator":
        a, = args
        require(node["opcode"] == "-" and not node["isPostfix"] and a["kind"] == "IntegerLiteral"
                and ctype(a) == t == ".i32", "expected negation of an int literal")
        return f'(.op {t} "-" (.num {t} 0) {read(a)})'
    if kind == "ConditionalOperator":
        cond, yes, no = args
        require(ctype(cond) == ".i32" and ctype(yes) == ctype(no) == t == ".u64", "unsupported conditional")
        return f"(.choose {read(cond)} {read(yes)} {read(no)})"
    if kind == "ParenExpr":
        a, = args
        require(ctype(a) == t, "parenthesized type mismatch")
        return read(a)
    if kind in {"ImplicitCastExpr", "CStyleCastExpr"}:
        a, = args
        cast = node["castKind"]
        if cast == "NoOp" or (cast == "LValueToRValue" and a["kind"] == "DeclRefExpr"):
            require(ctype(a) == t, "non-identity scalar conversion")
            return read(a)
        require(cast == "IntegralCast" and ctype(a) == ".i32" and t == ".u64", f"unsupported cast {cast}")
        return f"(.cast {t} {read(a)})"
    if kind == "CallExpr":
        callee, arg = args
        fn, = callee["inner"]
        require(callee["kind"] == "ImplicitCastExpr" and callee["castKind"] == "FunctionToPointerDecay"
                and fn["kind"] == "DeclRefExpr" and fn["referencedDecl"]["kind"] == "FunctionDecl"
                and fn["referencedDecl"]["id"] == callee_id and fn["referencedDecl"]["name"] == NAMES[0]
                and ctype(arg) == t == ".u64", "unexpected call target or signature")
        return f'(.call {t} "compressBound_z" [{read(arg)}])'
    raise ValueError(f"unsupported C expression {kind}")


def statements(body, outer, callee_id):
    require(body["kind"] == "CompoundStmt", "expected a block")
    scope = outer.copy()
    result = []
    for node in body.get("inner", []):
        kind = node["kind"]
        if kind == "IfStmt":
            cond, yes, no = node["inner"]
            require(ctype(cond) == ".i32", "expected an int condition")
            result.append(f".branch {expr(cond, scope, callee_id)} {statements(yes, scope, callee_id)} "
                          f"{statements(no, scope, callee_id)}")
            continue
        value, = node["inner"]
        if kind == "ReturnStmt":
            require(ctype(value) == ".u64", "expected unsigned long return")
            result.append(f".ret {expr(value, scope, callee_id)}")
        else:
            require(kind == "DeclStmt" and value["kind"] == "VarDecl" and value.get("init") == "c"
                    and "storageClass" not in value, f"unsupported statement {kind}")
            init, = value["inner"]
            name, t = local_name(value), ctype(value)
            require(all(key != name for key, _ in scope.values()) and ctype(init) == t, "unsupported binding")
            result.append(f".decl {t} {name} (some {expr(init, scope, callee_id)})")
            scope[value["id"]] = (name, t)
    return "[" + ", ".join(result) + "]"


def extract(data, folder, cc, flags):
    nodes = clang(data, flags, folder, compiler=cc, name="compressBound")
    definitions = {}
    for node in nodes:
        name = node.get("name")
        if name not in NAMES or node["kind"] != "FunctionDecl" or not function_body(node):
            continue
        loc = location(node["loc"])
        if "includedFrom" in loc:
            continue
        offset = loc["offset"]
        require(data[offset:offset + loc["tokLen"]] == name.encode(), "definition outside main source")
        require(name not in definitions and node["type"]["qualType"] in SIGNATURES[name]
                and "storageClass" not in node and node.get("mangledName") == name, f"unexpected ABI for {name}")
        definitions[name] = node
    require(set(definitions) == set(NAMES), "missing LP64 bound definition")
    emitted = []
    for name in NAMES:
        param, body = definitions[name]["inner"]
        require(param["kind"] == "ParmVarDecl" and ctype(param) == ".u64" and not param.get("inner"),
                f"unsupported parameter for {name}")
        key = local_name(param)
        block = statements(body, {param["id"]: (key, ".u64")}, definitions[NAMES[0]]["id"])
        emitted.append(f'([({key}, .u64)], {block})')
    return emitted, definitions[NAMES[0]]


def mutate_shift(data, function):
    literals = []
    for node in objects(function):
        if node.get("kind") == "BinaryOperator" and node["opcode"] == ">>":
            count = node["inner"][1]
            while count["kind"] == "ParenExpr":
                count, = count["inner"]
            if count["kind"] == "IntegerLiteral" and count["value"] == "12":
                literals.append(count)
    require(len(literals) == 1, "expected a unique shift by 12 in compressBound_z")
    literal, = literals
    loc = literal["range"]["begin"]
    require("offset" in loc and "includedFrom" not in loc and "expansionLoc" not in loc,
            "shift mutation requires a literal in the translation unit")
    start, length = loc["offset"], loc["tokLen"]
    replacement = b"11UL" if ctype(literal) == ".u64" else b"11"
    return data[:start] + replacement + data[start + length:]


def check_tree(work, label, trees, *, expect_mismatch=False):
    names = {"reference": ("original_compressBound_z", "original_compressBound"),
             "lean": ("standalone_compressBound_z", "compressBound_c")}[label]
    check_declarations(work, label, "Lean2C.OriginalBounds", "Lean2C.OriginalBounds Lean2C.Soundness",
                       names, trees, expect_mismatch=expect_mismatch)


def check_declarations(work, label, module, namespaces, names, trees, *, expect_mismatch=False):
    source = f"import {module}\nopen {namespaces}\n"
    require(len(names) == len(trees), "missing C certificate")
    source += "".join(f"example : {name} = {tree} := rfl\n" for name, tree in zip(names, trees))
    path = work / "Check.lean"
    path.write_text(source)
    proc = subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", path], cwd=ROOT,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if expect_mismatch:
        require(proc.returncode != 0 and ":3:" in proc.stdout and "Type mismatch" in proc.stdout,
                f"{label} mutation did not give the expected kernel mismatch\n{proc.stdout}")
    else:
        require(proc.returncode == 0, proc.stdout)


def main():
    subprocess.run(["lake", "build", "--wfail", "Lean2C.OriginalBounds"], cwd=ROOT, check=True)
    subprocess.run(["lake", "env", "leanchecker", "--fresh", "Lean2C.OriginalBounds"], cwd=ROOT, check=True)
    with tempfile.TemporaryDirectory(prefix="zlib-source-bounds-") as tmp:
        work = Path(tmp)
        inputs = prepare_inputs(work, pinned=True)
        for label in ("reference", "lean"):
            folder = work / label
            data = (folder / "compress.c").read_bytes()
            trees, bound_z = extract(data, folder, inputs.compiler, inputs.flags)
            check_tree(work, label, trees)
            changed = mutate_shift(data, bound_z)
            altered, _ = extract(changed, folder, inputs.compiler, inputs.flags)
            check_tree(work, label, altered, expect_mismatch=True)
            print(f"{label}/compress.c: both bound definitions checked; shift mutation rejected")


if __name__ == "__main__":
    main()
