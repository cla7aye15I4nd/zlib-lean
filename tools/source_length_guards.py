"""Check the argument-validation prefixes of the two one-shot zlib entry points."""
import json
from pathlib import Path
import subprocess
import tempfile

from archive import prepare_inputs
from ast_compare import clang, function_body, location
from reference import ROOT
from source_bounds import check_declarations, local_name, require

MODULE = "Lean2C.OriginalLengthGuards"
ENTRIES = (("compress.c", "compress2_z", "Compress"), ("uncompr.c", "uncompress2_z", "Uncompress"))
TYPES = {
    "int": ".i32", "long": ".i64", "unsigned long": ".u64",
    "unsigned int": ".u32", "const unsigned int": ".u32",
    "struct z_stream_s": '(.named "z_stream")',
    "void *": "(.ptr .void)",
    "voidpf (*)(voidpf, uInt, uInt)": '(.named "alloc_func")',
    "void *(*)(void *, unsigned int, unsigned int)": '(.named "alloc_func")',
    "void (*)(voidpf, voidpf)": '(.named "free_func")',
    "void (*)(void *, void *)": '(.named "free_func")',
    "uLong *": "(.ptr .u64)", "z_size_t *": "(.ptr .u64)", "unsigned long *": "(.ptr .u64)",
    "Bytef *": "(.ptr .u8)", "const Bytef *": "(.ptr .u8)",
    "unsigned char *": "(.ptr .u8)", "const unsigned char *": "(.ptr .u8)",
}


def ctype(node):
    ty = node["type"]
    name = ty.get("desugaredQualType", ty["qualType"])
    require(name in TYPES, f"unsupported guard operand type {name}")
    return TYPES[name]


def expr(node, scope):
    children = node.get("inner", [])
    kind, ty = node["kind"], ctype(node)
    if kind == "ParenExpr":
        child, = children
        require(ctype(child) == ty, "parentheses changed type")
        return expr(child, scope)
    if kind == "IntegerLiteral":
        n = int(node["value"])
        require(not children and ty in {".i32", ".u32", ".u64"} and 0 <= n <= 0x7fffffff, "unexpected scalar literal")
        return f"(.num {ty} {n})"
    if kind == "DeclRefExpr":
        decl = node["referencedDecl"]
        name = local_name(decl)
        require(not children and scope.get(decl["id"]) == (name, ty) and ctype(decl) == ty,
                "guard refers to a different variable")
        return f"(.var {ty} {name})"
    if kind == "MemberExpr":
        base, = children
        if node["isArrow"]:
            while base["kind"] == "ParenExpr":
                base, = base["inner"]
            require(base["kind"] == "UnaryOperator" and base["opcode"] == "&", "expected &local")
            base, = base["inner"]
        member = node["name"]
        require(base["kind"] == "DeclRefExpr" and ctype(base) == '(.named "z_stream")'
                and {"next_out": "(.ptr .u8)", "next_in": "(.ptr .u8)", "avail_in": ".u32", "avail_out": ".u32",
                     "reserved": ".u64", "opaque": "(.ptr .void)", "zalloc": '(.named "alloc_func")',
                     "zfree": '(.named "free_func")'}.get(member) == ty,
                "unexpected stream member")
        return f"(.field {ty} {expr(base, scope)} {json.dumps(member)})"
    if kind == "CStyleCastExpr":
        child, = children
        if node["castKind"] == "NoOp":
            require(ctype(child) == ty == "(.ptr .u8)", "expected byte pointer qualification cast")
        elif node["castKind"] == "BitCast":
            place = child
            while place["kind"] == "ParenExpr":
                place, = place["inner"]
            require(ty == "(.ptr .u8)" and ctype(child) == "(.ptr .u64)" and place["kind"] == "UnaryOperator"
                    and place["opcode"] == "&", "expected byte view of a length member address")
        elif node["castKind"] == "NullToPointer":
            require(child["kind"] == "IntegerLiteral" and ctype(child) == ".i32" and child["value"] == "0"
                    and ty in {'(.named "alloc_func")', '(.named "free_func")', "(.ptr .void)"}, "invalid null pointer")
        else:
            require(node["castKind"] == "IntegralCast" and (ctype(child), ty) in
                    {(".i64", ".u64"), (".u64", ".u32"), (".u32", ".u64"), (".u64", ".i32")},
                    "unexpected integral conversion")
        return f"(.cast {ty} {expr(child, scope)})"
    if kind == "UnaryExprOrTypeTraitExpr":
        require(node["name"] == "sizeof" and not children and ty == ".u64"
                and node["argType"].get("desugaredQualType") == "struct z_stream_s", "unexpected sizeof")
        # definition() appends a target-compiled static assertion for this type.
        return "(.num .u64 112)"
    if kind == "ConditionalOperator":
        cond, yes, no = children
        require(ctype(cond) in {".i32", ".u64"} and ctype(yes) == ctype(no) == ty
                and ty in {".i32", ".u32", "(.ptr .u8)"}, "unexpected conditional types")
        return f"(.choose {expr(cond, scope)} {expr(yes, scope)} {expr(no, scope)})"
    if kind == "ImplicitCastExpr":
        child, = children
        cast = node["castKind"]
        if cast == "NoOp":
            require(ctype(child) == ty == "(.ptr .u8)", "expected byte pointer qualification cast")
            return f"(.cast {ty} {expr(child, scope)})"
        if cast == "LValueToRValue":
            require(ctype(child) == ty and child["valueCategory"] == "lvalue", "invalid lvalue read")
            return expr(child, scope)
        literal = child["kind"] == "IntegerLiteral" and ctype(child) == ".i32"
        null_pointer = literal and child["value"] == "0" and (ty.startswith("(.ptr") or
                                                       ty in {'(.named "alloc_func")', '(.named "free_func")'})
        integer = (literal and ty in {".u32", ".u64"}) or (ctype(child), ty) == (".u32", ".u64")
        require((cast == "NullToPointer" and null_pointer) or (cast == "IntegralCast" and integer),
                "unexpected cast")
        return f"(.cast {ty} {expr(child, scope)})"
    if kind == "UnaryOperator":
        child, = children
        require(not node["isPostfix"], "unexpected postfix expression")
        if node["opcode"] == "&":
            require(ty == "(.ptr .u64)" and ctype(child) == ".u64" and child["kind"] == "MemberExpr"
                    and child["name"] == "reserved", "expected reserved member address")
            return f"(.addr {expr(child, scope)})"
        if node["opcode"] == "*":
            require(ty == ".u64" and ctype(child) == "(.ptr .u64)", "expected unsigned long lvalue")
            return f"(.load .u64 {expr(child, scope)})"
        require(node["opcode"] == "-" and ty == ".i32" and child["kind"] == "IntegerLiteral"
                and ctype(child) == ".i32", "unexpected signed expression")
        return f'(.op .i32 "-" (.num .i32 0) {expr(child, scope)})'
    require(kind == "BinaryOperator", f"unexpected scalar expression {kind}")
    a, b = children
    op = node["opcode"]
    if op == "+" and ty == ctype(a) == ctype(b) == ".u64":
        return f'(.op .u64 "+" {expr(a, scope)} {expr(b, scope)})'
    if op == "-":
        require(ctype(a) == ctype(b) and (ctype(a), ty) in {("(.ptr .u8)", ".i64"), (".u64", ".u64")},
                "unexpected subtraction types")
        return f'(.op {ty} "-" {expr(a, scope)} {expr(b, scope)})'
    require(ty == ".i32" and ctype(a) == ctype(b) and ((op in {"&&", "||", "==", "!="} and ctype(a) == ".i32")
            or (op in {">", ">="} and ctype(a) == ".u64")
            or (op in {"==", "!="} and ctype(a) in {".u32", ".u64"})
            or (op == "==" and ctype(a).startswith("(.ptr"))), "unexpected binary operands")
    return f"(.op .i32 {json.dumps(op)} {expr(a, scope)} {expr(b, scope)})"


def block(node, scope):
    scope = scope.copy()
    children = node.get("inner", []) if node["kind"] == "CompoundStmt" else [node]
    return "[" + ", ".join(statement(st, scope) for st in children) + "]"


def statement(node, scope):
    kind, children = node["kind"], node.get("inner", [])
    if kind == "IfStmt":
        cond, yes, *no = children
        require(ctype(cond) == ".i32" and len(no) <= 1, "invalid guard branch")
        otherwise = block(no[0], scope) if no else "[]"
        return f".branch {expr(cond, scope)} {block(yes, scope)} {otherwise}"
    if kind == "ReturnStmt":
        val, = children
        require(ctype(val) == ".i32", "expected a signed error code")
        return f".ret {expr(val, scope)}"
    if kind == "DeclStmt":
        var, = children
        name, ty = local_name(var), ctype(var)
        require(var["kind"] == "VarDecl" and "storageClass" not in var and name not in {n for n, _ in scope.values()},
                "expected a fresh automatic scalar")
        if not var.get("inner"):
            require("init" not in var and ty in {"(.ptr .u8)", ".i32", ".u32", ".u64"}, "unexpected uninitialized scalar")
            scope[var["id"]] = (name, ty)
            return f".decl {ty} {name} none"
        val, = var["inner"]
        require(var.get("init") == "c", "unexpected initializer")
        require(ctype(val) == ty, "invalid local type")
        initializer = expr(val, scope)
        scope[var["id"]] = (name, ty)
        return f".decl {ty} {name} (some {initializer})"
    if kind == "CompoundAssignOperator":
        lhs, rhs = children
        op = node["opcode"]
        local = lhs["kind"] == "DeclRefExpr"
        # Reading a bare pointer parameter twice cannot repeat side effects.
        pointer = lhs.get("inner", [{}])[0]
        referent = pointer.get("inner", [{}])[0]
        deref = (lhs["kind"] == "UnaryOperator" and lhs["opcode"] == "*" and not lhs["isPostfix"]
                 and pointer["kind"] == "ImplicitCastExpr" and pointer["castKind"] == "LValueToRValue"
                 and referent.get("kind") == "DeclRefExpr" and referent["referencedDecl"]["kind"] == "ParmVarDecl")
        require(((local and op in {"+=", "-="}) or (deref and op == "-="))
                and ctype(lhs) == ctype(rhs) == ctype(node) == ".u64" and
                all(ctype({"type": node[k]}) == ".u64" for k in ("computeLHSType", "computeResultType")),
                "expected unsigned long compound assignment to a local or length parameter pointee")
        left = expr(lhs, scope)
        return f'.assign {left} (.op .u64 "{op[0]}" {left} {expr(rhs, scope)})'
    require(kind == "BinaryOperator" and node["opcode"] == "=", "unexpected scalar side effect")
    lhs, rhs = children
    local = lhs["kind"] == "DeclRefExpr" and lhs["referencedDecl"]["kind"] in {"VarDecl", "ParmVarDecl"}
    scalar_store = lhs["kind"] == "UnaryOperator" and lhs["opcode"] == "*" and ctype(lhs) == ".u64"
    require((local or scalar_store or lhs["kind"] == "MemberExpr") and ctype(lhs) == ctype(rhs) == ctype(node),
            "unexpected assignment")
    return f".assign {expr(lhs, scope)} {expr(rhs, scope)}"


def definition(data, directory, cc, flags, fn):
    src = "unsigned long *" if fn == "uncompress2_z" else "unsigned long, int"
    sig = f"int (*)(unsigned char *, unsigned long *, const unsigned char *, {src})"
    assertion = f'\n_Static_assert(__builtin_types_compatible_p(__typeof__(&{fn}), {sig}), "signature");\n'
    assertion += '_Static_assert(sizeof(z_stream) == 112, "unexpected stream size");\n'
    if fn == "uncompress2_z":
        assertion += '_Static_assert(__builtin_types_compatible_p(__typeof__(((z_stream *)0)->reserved), unsigned long), "reserved type");\n'
        assertion += '_Static_assert(__builtin_offsetof(z_stream, reserved) == 104, "unexpected reserved offset");\n'
        for name, args in (("inflateInit_", "z_stream *, const char *, int"),
                           ("inflate", "z_stream *, int"), ("inflateEnd", "z_stream *")):
            assertion += f'_Static_assert(__builtin_types_compatible_p(__typeof__(&{name}), int (*)({args})), "callee");\n'
    if fn == "compress2_z":
        for name, args in (("deflateInit_", "z_stream *, int, const char *, int"),
                           ("deflate", "z_stream *, int"), ("deflateEnd", "z_stream *")):
            assertion += f'_Static_assert(__builtin_types_compatible_p(__typeof__(&{name}), int (*)({args})), "callee");\n'
    nodes = clang(data + assertion.encode(), flags, directory, compiler=cc, name=fn)
    f, = [node for node in nodes if node.get("name") == fn and node["kind"] == "FunctionDecl" and function_body(node)]
    pos = location(f["loc"])
    require("includedFrom" not in pos and data[pos["offset"]:pos["offset"] + pos["tokLen"]] == fn.encode(),
            "expected definition in archive input")
    params = [n for n in f["inner"] if n["kind"] == "ParmVarDecl"]
    names = ["dest", "destLen", "source", "sourceLen"] + (["level"] if fn == "compress2_z" else [])
    require([p["name"] for p in params] == names, "unexpected parameter order")
    scope = {p["id"]: (local_name(p), ctype(p)) for p in params}
    return function_body(f)["inner"], scope


def prefix(data, directory, cc, flags, fn, generated):
    statements, scope = definition(data, directory, cc, flags, fn)
    body = iter(statements)
    # Prefix begins after the administrative declarations. The sole initializer
    # here is UINT_MAX, spelled (uInt)-1 or 4294967295U on the pinned build.
    for name in (["strm" if fn == "compress2_z" else "stream", "max"] if generated else
                 ["stream", "err", "max", "left"] if fn == "compress2_z" else ["stream", "err", "max", "len"]):
        decl = next(body)
        require(decl["kind"] == "DeclStmt", "operation before validation")
        vars_ = decl["inner"]
        expected = [name, "left"] if not generated and name == "len" else [name]
        require([v["name"] for v in vars_] == expected and all(v["kind"] == "VarDecl" and "storageClass" not in v
                for v in vars_), "unexpected prelude declarations")
        for v in vars_:
            ty = v["type"].get("desugaredQualType", v["type"]["qualType"])
            if v["name"] == "max":
                require(ty in {"unsigned int", "const unsigned int"}, "invalid max type")
                init, = v["inner"]
                if generated:
                    require(init["kind"] == "IntegerLiteral" and init["value"] == "4294967295",
                            "unexpected max initializer")
                else:
                    require(init["kind"] == "CStyleCastExpr" and init["castKind"] == "IntegralCast",
                            "unexpected max cast")
                    minus, = init["inner"]
                    require(minus["kind"] == "UnaryOperator" and minus["opcode"] == "-" and
                            ctype(minus) == ".i32", "expected -1")
                    one, = minus["inner"]
                    require(one["kind"] == "IntegerLiteral" and one["value"] == "1" and ctype(one) == ".i32",
                            "expected integer one")
            else:
                require(not v.get("inner") and ty in {"struct z_stream_s", "int", "unsigned long"},
                        "unexpected initializer or variably sized declaration")
    if generated:
        init, guard, gate = next(body), next(body), next(body)
        require(gate["kind"] == "IfStmt", "missing return dispatch")
        cond, rejected, continuation = gate["inner"]
        require(continuation["kind"] == "CompoundStmt" and continuation.get("inner"), "missing accepted continuation")
        statements = [statement(init, scope), statement(guard, scope),
                      f".branch {expr(cond, scope)} {block(rejected, scope)} []"]
        ret, = rejected["inner"]
    else:
        guard = next(body)
        require(guard["kind"] == "IfStmt" and len(guard["inner"]) == 2, "expected original early return")
        statements = [statement(guard, scope)]
        _, ret = guard["inner"]
    require(ret["kind"] == "ReturnStmt", "validation does not return")
    return "[" + ", ".join(statements) + "]", guard, location(ret["range"]["begin"])["offset"]


def span(node):
    begin = location(node["range"]["begin"])
    end = location(node["range"]["end"])
    return begin["offset"], end["offset"] + end["tokLen"]


def change_read_order(data, guard, generated):
    if generated:
        # Move a typed read into the earliest refusal branch. Its value is
        # unused, but the source evaluator must still check the dereference.
        assignment = guard["inner"][1]["inner"][0]
        require(assignment["kind"] == "BinaryOperator" and assignment["opcode"] == "=", "expected bad flag")
        where = location(assignment["range"]["begin"])["offset"]
        return data[:where] + b"unsigned long eager = *destLen; " + data[where:]
    # The same disjuncts now test the destination first.
    outer = guard["inner"][0]
    require(outer["kind"] == "BinaryOperator" and outer["opcode"] == "||", "expected short-circuit OR")
    a, b = outer["inner"]
    first, mid = span(a)
    right, last = span(b)
    return data[:first] + b"(" + data[right:last] + b") || (" + data[first:mid] + b")" + data[last:]


def cases(directory, inputs, label):
    for filename, fn, suffix in ENTRIES:
        generated = label == "lean"
        name = ("standalone" if generated else "original") + suffix
        data = (directory / filename).read_bytes()
        tree, guard, ret = prefix(data, directory, inputs.compiler, inputs.flags, fn, generated)
        yield name, tree, False
        reordered = change_read_order(data, guard, generated)
        yield name, prefix(reordered, directory, inputs.compiler, inputs.flags, fn, generated)[0], True
        require(data[ret:ret + 6] == b"return", "error return outside input")
        changed = data[:ret] + b"return (-3)" + data[data.index(b";", ret):]
        yield name, prefix(changed, directory, inputs.compiler, inputs.flags, fn, generated)[0], True
        start = data.index(fn.encode() + b"(")
        compare = data.index(b" > ", start, ret)
        changed = data[:compare] + b" >= " + data[compare + 3:]
        yield name, prefix(changed, directory, inputs.compiler, inputs.flags, fn, generated)[0], True


def main():
    subprocess.run(["lake", "build", "--wfail", MODULE], cwd=ROOT, check=True)
    subprocess.run(["lake", "env", "leanchecker", "--fresh", MODULE], cwd=ROOT, check=True)
    with tempfile.TemporaryDirectory(prefix="zlib-length-guards-") as tmp:
        work = Path(tmp)
        inputs = prepare_inputs(work, pinned=True)
        for label in ("reference", "lean"):
            for name, tree, mismatch in cases(work / label, inputs, label):
                check_declarations(work, label, MODULE, MODULE, [name], [tree], expect_mismatch=mismatch)
                print(f"{name}: {'mutation rejected' if mismatch else 'guard checked'}")


if __name__ == "__main__":
    main()
