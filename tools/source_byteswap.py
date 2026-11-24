"""Import and check both typed byte_swap bodies from the pinned archive inputs."""
import json
from pathlib import Path
import subprocess
import tempfile

from archive import prepare_inputs
from ast_compare import clang, function_body, location, objects
from reference import ROOT
from source_bounds import check_declarations, require


TYPES = {"unsigned int": ".u32", "int": ".i32", "long": ".i64"}
MODULE = "Lean2C.OriginalByteSwap"


def ctype(node):
    ty = node["type"]
    name = ty.get("desugaredQualType", ty["qualType"])
    require(name in TYPES, f"unexpected byte_swap operand type {name}")
    return TYPES[name]


def expression(node, param_id):
    kind, ty = node["kind"], ctype(node)
    args = node.get("inner", [])
    if kind == "DeclRefExpr":
        ref = node["referencedDecl"]
        require(not args and ref["kind"] == "ParmVarDecl" and ref["id"] == param_id and
                ref["name"] == "word" and ctype(ref) == ty == ".u32", "unexpected binding")
        return '(.var .u32 "word")'
    if kind == "IntegerLiteral":
        n = int(node["value"])
        bits = {".i32": 31, ".u32": 32, ".i64": 63}[ty]
        require(not args and 0 <= n < 2 ** bits, "integer literal out of range")
        return f"(.num {ty} {n})"
    if kind == "BinaryOperator":
        left, right = args
        op = node["opcode"]
        require(ctype(left) == ty and ty in {".u32", ".i64"} and
                ((op in {"&", "|"} and ctype(right) == ty) or
                 (op in {"<<", ">>"} and ctype(right) == ".i32")), f"unexpected types for {op}")
        return f"(.op {ty} {json.dumps(op)} {expression(left, param_id)} {expression(right, param_id)})"
    child, = args
    if kind == "ParenExpr" or (kind == "ImplicitCastExpr" and node["castKind"] == "LValueToRValue"
                               and child["kind"] == "DeclRefExpr"):
        require(ctype(child) == ty, "unexpected conversion")
        return expression(child, param_id)
    require(kind == "ImplicitCastExpr" and node["castKind"] == "IntegralCast", f"unexpected {kind}")
    return f"(.cast {ty} {expression(child, param_id)})"


def extract(data, folder, compiler, flags):
    nodes = clang(data, flags, folder, compiler=compiler, name="byte_swap")
    fn, = [n for n in nodes if n.get("kind") == "FunctionDecl" and n.get("name") == "byte_swap" and
           function_body(n) and "includedFrom" not in location(n["loc"])]
    loc = location(fn["loc"])
    require(data[loc["offset"]:loc["offset"] + loc["tokLen"]] == b"byte_swap" and
            fn.get("storageClass") == "static" and fn["type"]["qualType"] == "z_word_t (z_word_t)",
            "expected static byte_swap in main translation unit")
    param, body = fn["inner"]
    require(param["kind"] == "ParmVarDecl" and param["name"] == "word" and not param.get("inner")
            and ctype(param) == ".u32" and body["kind"] == "CompoundStmt", "unexpected function signature")
    ret, = body["inner"]
    value, = ret["inner"]
    require(ret["kind"] == "ReturnStmt" and ctype(value) == ".u32", "expected one unsigned return")
    return f'([("word", .u32)], [.ret {expression(value, param["id"])}])', value


def variants(data, folder, compiler, flags, label):
    tree, body = extract(data, folder, compiler, flags)
    yield "source", tree
    shifts = (n for n in objects(body) if n.get("kind") == "BinaryOperator" and n["opcode"] == ">>")
    count, = [s["inner"][1] for s in shifts if s["inner"][1].get("value") == "24"]
    mutations = [(count, b"24", b"23", "shift count")]
    if label == "lean":
        mask, = [n for n in objects(body) if n.get("kind") == "IntegerLiteral" and n["value"] == "4278190080"]
        mutations.append((mask, b"4278190080", b"4278190080U", "mask type"))
    for node, before, after, description in mutations:
        loc = node["range"]["begin"]
        offset = loc["offset"]
        require("includedFrom" not in loc and data[offset:offset + loc["tokLen"]] == before,
                f"expected a literal in the source file for {description}")
        altered = data[:offset] + after + data[offset + len(before):]
        yield description, extract(altered, folder, compiler, flags)[0]


def main():
    subprocess.run(["lake", "build", "--wfail", MODULE], cwd=ROOT, check=True)
    subprocess.run(["lake", "env", "leanchecker", "--fresh", MODULE], cwd=ROOT, check=True)
    with tempfile.TemporaryDirectory(prefix="zlib-source-byteswap-") as tmp:
        work = Path(tmp)
        inputs = prepare_inputs(work, pinned=True)
        for label, name in (("reference", "original"), ("lean", "standalone")):
            folder = work / label
            data = (folder / "crc32.c").read_bytes()
            for variant, tree in variants(data, folder, inputs.compiler, inputs.flags, label):
                check_declarations(work, label, MODULE, MODULE, [name], [tree], expect_mismatch=variant != "source")
                print(f"{label}/crc32.c byte_swap: {variant} {'checked' if variant == 'source' else 'rejected'}")


if __name__ == "__main__":
    main()
