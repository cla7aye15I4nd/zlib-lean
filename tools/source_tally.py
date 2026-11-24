"""Check symbol stores and the two putShortMSB checksum pairs in both pinned deflate sources."""
from pathlib import Path
import re
import subprocess
import tempfile

from archive import prepare_inputs
from ast_compare import clang, function_body
from reference import ROOT
from source_bounds import require
from source_restore import ULONG, expression, typed, variable, walk


# Site order in the active, non-LIT_MEM implementation.
STRATEGIES = {"deflate_fast": ("dist", "lit"), "deflate_slow": ("dist", "lit", "lit"),
              "deflate_rle": ("dist", "lit"), "deflate_huff": ("lit",)}
BYTE = {"unsigned char"}
BYTE_POINTER = {"uchf *", "Bytef *", "unsigned char *"}
UINT = {"unsigned int"}


def member(node, state, types):
    node = expression(node)
    require(node.get("kind") == "MemberExpr" and node["isArrow"], "expected a state field")
    require(variable(expression(node["inner"][0]))["id"] == state, "wrong state pointer")
    typed(node, types)
    field = node["name"]
    require(field.isascii() and field.isidentifier(), "invalid C member name")
    return field, node["range"]["end"]["offset"]


def byte_operand(node, variables, locals_in_function):
    """Interpret the byte conversion of the captured macro arguments on LP64."""
    typed(node, BYTE)
    value = expression(node)
    if value.get("castKind") == "IntegralCast":
        value = expression(value["inner"][0])
    if value["kind"] == "IntegerLiteral":
        typed(value, {"int"})
        return f"({int(value['value'])} : UInt8)"
    if value.get("opcode") == ">>":
        left, count = map(expression, value["inner"])
        typed(value, {"int"})
        require(left.get("castKind") == "IntegralCast", "expected a promoted 16-bit distance")
        typed(left, {"int"})
        left = expression(left["inner"][0])
        typed(count, {"int"})
        require(count["kind"] == "IntegerLiteral" and 0 <= int(count["value"]) < 32, "invalid shift")
        amount = int(count["value"])
    else:
        left, amount = value, None
    decl = variable(left)
    require(decl["id"] in locals_in_function, "expected a local macro argument")
    name = re.sub(r"_\d+$", "", decl["name"])
    require(name in {"cc", "dist", "len"}, "unexpected macro operand")
    require(variables.setdefault(name, decl["id"]) == decl["id"], "different locals in the same tally")
    typed(left, {"unsigned short"} if name == "dist" else BYTE)
    if name == "dist":
        return "dist.toUInt8" if amount is None else f"((dist.toUInt32 >>> {amount}).toUInt8)"
    require(amount is None, "only a distance is shifted")
    return name


def store_at(stmts, start, state):
    if start >= len(stmts):
        return None
    stmt = stmts[start]
    capture = None
    end = start + 1
    if stmt["kind"] == "DeclStmt" and len(stmt.get("inner", [])) == 1:
        capture = stmt["inner"][0]
        if capture.get("init") != "c" or end >= len(stmts):
            return None
        stmt = stmts[end]
        end += 1
    if stmt.get("opcode") != "=":
        return None
    lhs, rhs = stmt["inner"]
    if lhs["kind"] != "ArraySubscriptExpr":
        return None
    ptr, post = lhs["inner"]
    if post.get("opcode") != "++":
        return None
    if capture is not None:
        used = expression(rhs)
        if used["kind"] != "DeclRefExpr" or variable(used)["id"] != capture["id"]:
            return None
        typed(capture, BYTE)
        rhs, = capture["inner"]
    require(post["kind"] == "UnaryOperator" and post.get("isPostfix"), "expected the old symbol index")
    typed(post, UINT)
    typed(lhs, BYTE)
    base, offset = member(ptr, state, BYTE_POINTER)
    index, _ = member(post["inner"][0], state, UINT)
    return (offset, base, index, rhs), end


def triples(data, folder, inputs, fn):
    nodes = clang(data, inputs.flags, folder, compiler=inputs.compiler, name=fn)
    fn_decl, = [n for n in nodes if n.get("name") == fn and function_body(n)]
    state, flush = [n for n in fn_decl["inner"] if n["kind"] == "ParmVarDecl"]
    typed(state, {"deflate_state *"})
    typed(flush, {"int"})
    groups = []
    for block in walk(function_body(fn_decl)):
        if block.get("kind") != "CompoundStmt":
            continue
        stmts = block.get("inner", [])
        i = 0
        while i < len(stmts):
            site = store_at(stmts, i, state["id"])
            if site is None:
                i += 1
                continue
            first, i = site
            group = [first]
            for _ in range(2):
                following = store_at(stmts, i, state["id"])
                require(following is not None, "expected three consecutive symbol stores")
                store, i = following
                group.append(store)
            groups.append(group)
    groups.sort(key=lambda group: group[0][0])
    require(len(groups) == len(STRATEGIES[fn]), f"{fn}: wrong number of tally sites")
    locals_in_function = {n["id"] for n in walk(function_body(fn_decl)) if n.get("kind") == "VarDecl"}
    return groups, locals_in_function


def certify(lines, group, kind, locals_in_function):
    variables = {}
    params = "(cc : UInt8)" if kind == "lit" else "(dist : UInt16) (len : UInt8)"
    lines.append(f"example (s : DeflateStatePtr) {params} : (do")
    for _, base, index, rhs in group:
        value = byte_operand(rhs, variables, locals_in_function)
        lines += ["  (do", "    let d ← ldDeflateState s", f"    let p ← Ptr.add d.«{base}» d.«{index}».toNat",
                  f"    md s (fun d' => {{d' with «{index}» := d'.«{index}» + 1}})",
                  f"    store8 p {value})"]
    expected = ["0", "0", "cc"] if kind == "lit" else ["dist.toUInt8", "(dist >>> 8).toUInt8", "len"]
    lines += [") = (do", *(f"  put_symbol_byte s {value}" for value in expected), ") := by"]
    if kind == "dist":
        lines += ["  have high : (dist.toUInt32 >>> 8).toUInt8 = (dist >>> 8).toUInt8 := by bv_decide",
                  "  simp only [high]"]
    lines.append("  rfl")


def verify(path, lines, expected_errors=()):
    path.write_text("\n".join(lines) + "\n")
    result = subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", path], cwd=ROOT,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if expected_errors:
        require(result.returncode != 0 and all(e in result.stdout for e in expected_errors), result.stdout)
    else:
        require(result.returncode == 0, result.stdout)


def check(data, folder, inputs, path, functions, *, reject=False):
    lines = ["import Std.Tactic.BVDecide", "import ZlibF.Zlib.«trees.c»", "open C Zlib.Trees"]
    offsets = {}
    for fn in functions:
        groups, locals_in_function = triples(data, folder, inputs, fn)
        for group, kind in zip(groups, STRATEGIES[fn], strict=True):
            certify(lines, group, kind, locals_in_function)
        offsets[fn] = groups[0][0][0]
    verify(path, lines, ("rfl", "failed") if reject else ())
    return offsets


def calls_short_msb(stmt):
    if stmt.get("kind") != "CallExpr":
        return False
    fn = stmt["inner"][0]
    if fn.get("castKind") == "FunctionToPointerDecay":
        fn, = fn["inner"]
    fn = expression(fn)
    if fn["kind"] != "DeclRefExpr":
        return False
    decl = variable(fn)
    return decl["kind"] == "FunctionDecl" and decl["name"] == "putShortMSB"


def checksum_pairs(data, folder, inputs, generated):
    roots = clang(data, inputs.flags, folder, name="deflate", compiler=inputs.compiler)
    fn, = [n for n in roots if n.get("kind") == "FunctionDecl" and n["name"] == "deflate" and function_body(n)]
    stream, flush = [n for n in fn["inner"] if n["kind"] == "ParmVarDecl"]
    typed(flush, {"int"})
    body = function_body(fn)
    state, = [n for n in walk(body) if n.get("kind") == "VarDecl" and n.get("name") == "s"]
    pairs = []
    for block in walk(body):
        stmts = block.get("inner", [])
        if block.get("kind") != "CompoundStmt" or len(stmts) != (6 if generated else 2):
            continue
        calls = stmts[2::3] if generated else stmts
        if not all(calls_short_msb(stmt) for stmt in calls):
            continue
        pair = []
        for i, call in enumerate(calls):
            _, ptr, arg = call["inner"]
            require(variable(expression(ptr))["id"] == state["id"], "wrong state in checksum write")
            cast = expression(arg)
            typed(cast, UINT)
            require(cast["kind"] == "CStyleCastExpr" and cast.get("castKind") == "IntegralCast",
                    "expected unsigned conversion of the checksum bits")
            operation = expression(cast["inner"][0])
            typed(operation, ULONG)
            op = operation.get("opcode")
            require(op in {">>", "&"}, "unexpected checksum operation")
            value, count = map(expression, operation["inner"])
            if count.get("castKind") == "IntegralCast":
                count = expression(count["inner"][0])
            require(count["kind"] == "IntegerLiteral", "expected a constant shift or mask")
            number = int(count["value"])
            require(0 <= number < (64 if op == ">>" else 1 << 64), "invalid checksum shift or mask")
            if generated:
                decl, assign = stmts[3 * i:3 * i + 2]
                require(decl["kind"] == "DeclStmt" and assign.get("opcode") == "=", "expected a fresh read")
                local, = decl["inner"]
                typed(local, ULONG)
                lhs, rhs = assign["inner"]
                require(variable(expression(lhs))["id"] == local["id"] == variable(value)["id"],
                        "checksum write does not use its immediately preceding read")
                value = rhs
            field, offset = member(value, stream["id"], ULONG)
            require(field in {"adler", "total_out"}, "unsupported stream field in checksum write")
            pair.append((field, op, number, offset))
        pairs.append(pair)
    require(len(pairs) == 2, "expected a checksum pair in the dictionary header and the zlib trailer")
    return pairs


def certify_checksum(pair, path, *, reject=False):
    lines = ["import ZlibF.Proof.«deflate.c.trailer-source»", "open C Zlib.Deflate Zlib.Deflate.Engine.Proofs",
             "example (strm : ZStreamPtr) (s : DeflateStatePtr) : (do"]
    for field, op, value, _ in pair:
        operator = ">>>" if op == ">>" else "&&&"
        lines.extend([f"  let a ← zrd strm (·.{field})", f"  putShortMSB s (a {operator} {value}).toUInt32"])
    lines.extend(["  : M Unit) = zlibTrailer strm s := by", "  unfold zlibTrailer",
                  "  with_reducible exact dictionary_header_reread_eq strm s"])
    verify(path, lines, ("Type mismatch",) if reject else ())


def check_checksum_pairs(folder, inputs, generated, path):
    data = (folder / "deflate.c").read_bytes()
    original = checksum_pairs(data, folder, inputs, generated)
    for pair in original:
        certify_checksum(pair, path)
    for offset in sorted((pair[1][3] for pair in original), reverse=True):
        require(data[offset:offset + 5] == b"adler", "expected the checksum field token")
        data = data[:offset] + b"total_out" + data[offset + 5:]
    for pair in checksum_pairs(data, folder, inputs, generated):
        certify_checksum(pair, path, reject=True)


def main():
    modules = ["ZlibF.Proof.«deflate.c.engine.tally-match»", "ZlibF.Proof.«deflate.c.trailer-source»"]
    subprocess.run(["lake", "build", "--wfail", *modules], cwd=ROOT, check=True)
    for module in modules:
        subprocess.run(["lake", "env", "leanchecker", "--fresh", module], cwd=ROOT, check=True)
    with tempfile.TemporaryDirectory(prefix="zlib-source-tally-") as tmp:
        work = Path(tmp)
        inputs = prepare_inputs(work, pinned=True)
        for name in ("reference", "lean"):
            folder = work / name
            data = subprocess.check_output([*inputs.compiler, *inputs.flags, "-E", "-P", "deflate.c"], cwd=folder)
            args = folder, inputs, work / "CheckTally.lean"
            offset = check(data, *args, STRATEGIES)["deflate_huff"]
            require(data[offset:offset + 7] == b"sym_buf", "expected actual buffer token")
            changed = data[:offset] + b"pending_buf" + data[offset + 7:]
            check(changed, *args, ["deflate_huff"], reject=True)
            print(f"{name}/deflate.c: eight tally sites checked, destination-buffer mutation rejected")
            check_checksum_pairs(folder, inputs, name == "lean", work / "CheckChecksum.lean")
            print(f"{name}/deflate.c: dictionary and trailer checksum pairs checked, both wrong fields rejected")


if __name__ == "__main__":
    main()
