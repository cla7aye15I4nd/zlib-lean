"""Check zError and its static string table in both pinned Linux translation units."""
import json
from pathlib import Path
import re
import subprocess
import tempfile

from archive import prepare_inputs
from ast_compare import clang, function_body, location
from reference import ROOT
from source_bounds import check_declarations, require


MODULE = "Lean2C.OriginalError"
TABLE_TYPE = "char *const[10]"


def typed(node, kind, ty):
    require(node["kind"] == kind and node["type"]["qualType"] == ty, f"expected {kind} of type {ty}")


def unparen(node):
    while node["kind"] == "ParenExpr":
        child, = node["inner"]
        require(node["type"] == child["type"], "parentheses changed operand type")
        node = child
    return node


def integer(node, scope):
    node = unparen(node)
    kind = node["kind"]
    require(node["type"]["qualType"] == "int", f"expected signed int in {kind}")
    children = node.get("inner", [])
    if kind == "IntegerLiteral":
        n = int(node["value"])
        require(not children and 0 <= n < 2 ** 31, "invalid int literal")
        return f"(.num .i32 {n})"
    if kind == "ImplicitCastExpr" and node["castKind"] == "LValueToRValue":
        child, = children
        ref = unparen(child)
        typed(ref, "DeclRefExpr", "int")
        decl = ref["referencedDecl"]
        require(decl["id"] in scope and scope[decl["id"]] == (decl["name"], decl["kind"]) and
                decl["type"]["qualType"] == "int", "index reads an unexpected declaration")
        return f'(.var .i32 {json.dumps(decl["name"])})'
    if kind == "UnaryOperator":
        child, = children
        require(node["opcode"] == "-" and not node["isPostfix"], "unexpected unary operation")
        return f'(.op .i32 "-" (.num .i32 0) {integer(child, scope)})'
    if kind == "BinaryOperator":
        left, right = children
        op = node["opcode"]
        require(op in {"<", ">", "-", "||"}, f"unexpected operator {op}")
        return f"(.op .i32 {json.dumps(op)} {integer(left, scope)} {integer(right, scope)})"
    if kind == "ConditionalOperator":
        cond, yes, no = children
        return f"(.choose {integer(cond, scope)} {integer(yes, scope)} {integer(no, scope)})"
    raise ValueError(f"unexpected signed expression {kind}")


def read_table(node, scope, ids):
    typed(node, "ImplicitCastExpr", "const char *")
    require(node["castKind"] == "NoOp", "unexpected return conversion")
    load, = node["inner"]
    typed(load, "ImplicitCastExpr", "char *")
    require(load["castKind"] == "LValueToRValue", "expected a pointer load")
    sub, = load["inner"]
    typed(sub, "ArraySubscriptExpr", "char *const")
    decay, index = sub["inner"]
    typed(decay, "ImplicitCastExpr", "char *const *")
    require(decay["castKind"] == "ArrayToPointerDecay", "expected table decay")
    table, = decay["inner"]
    typed(table, "DeclRefExpr", TABLE_TYPE)
    decl = table["referencedDecl"]
    require(decl["kind"] == "VarDecl" and decl["id"] in ids and decl["name"] == "z_errmsg", "wrong table")
    return f'(.index (.ptr .u8) (.var (.ptr (.ptr (.named "char"))) "z_errmsg") {integer(index, scope)})'


def literal(node):
    if node["kind"] == "CStyleCastExpr":
        typed(node, "CStyleCastExpr", "char *")
        require(node["castKind"] == "NoOp", "unexpected literal cast")
        node, = node["inner"]
    typed(node, "ImplicitCastExpr", "char *")
    require(node["castKind"] == "ArrayToPointerDecay", "expected literal decay")
    text, = node["inner"]
    value = json.loads(text["value"])
    require(re.fullmatch("[a-z ]*", value) is not None, "unexpected literal spelling")
    typed(text, "StringLiteral", f"char[{len(value) + 1}]")
    return value


def extract(data, folder, cc, flags):
    unit, = clang(data, flags, folder, compiler=cc)
    decls = unit["inner"]
    fn, = [n for n in decls if n["kind"] == "FunctionDecl" and n.get("name") == "zError" and function_body(n)]
    table, = [n for n in decls if n["kind"] == "VarDecl" and n.get("name") == "z_errmsg" and n.get("init")]
    for node in (fn, table):
        pos = location(node["loc"])
        require("includedFrom" not in pos and data[pos["offset"]:pos["offset"] + pos["tokLen"]] == node["name"].encode()
                and "storageClass" not in node, "unexpected external definition")
    typed(table, "VarDecl", TABLE_TYPE)
    init, = table["inner"]
    typed(init, "InitListExpr", TABLE_TYPE)
    strings = [literal(n) for n in init["inner"]]
    require(len(strings) == 10, "table initializer must supply all ten entries")
    table_ids = {table["id"]}
    by_id = {n["id"]: n for n in decls if n.get("id")}
    declaration = table
    while "previousDecl" in declaration:
        declaration = by_id[declaration["previousDecl"]]
        require(declaration["kind"] == "VarDecl" and declaration["name"] == "z_errmsg", "invalid table redeclaration")
        table_ids.add(declaration["id"])
    typed(fn, "FunctionDecl", "const char *(int)")
    param, body = fn["inner"]
    typed(param, "ParmVarDecl", "int")
    require(param["name"] == "err" and not param.get("inner") and body["kind"] == "CompoundStmt", "unexpected parameter")
    scope = {param["id"]: ("err", "ParmVarDecl")}
    statements = []
    *prefix, ret = body["inner"]
    if prefix:
        stmt, = prefix
        require(stmt["kind"] == "DeclStmt", "expected the generated temporary")
        temp, = stmt["inner"]
        typed(temp, "VarDecl", "int")
        require(temp["name"] == "i" and temp.get("init") == "c" and "storageClass" not in temp, "unexpected local")
        init_value, = temp["inner"]
        statements.append(f'(.decl .i32 "i" (some {integer(init_value, scope)}))')
        scope[temp["id"]] = ("i", "VarDecl")
    require(ret["kind"] == "ReturnStmt", "expected a return")
    expr, = ret["inner"]
    statements.append(f"(.ret {read_table(expr, scope, table_ids)})")
    return f'([("err", .i32)], [{", ".join(statements)}])', f'#[{", ".join(map(json.dumps, strings))}]', ret


def variants(data, folder, cc, flags):
    body, table, ret = extract(data, folder, cc, flags)
    yield "body", body
    yield "table", table
    loc = location(ret["range"]["begin"])
    require("includedFrom" not in loc and data[loc["offset"]:loc["offset"] + loc["tokLen"]] == b"return",
            "return mutation must begin in main source")
    end = data.index(b";", loc["offset"])
    altered = data[:loc["offset"]] + b"return z_errmsg[err]" + data[end:]
    yield "wrong index", extract(altered, folder, cc, flags)[0]
    require(data.count(b'"need dictionary"') == 1, "expected first literal in main source")
    altered = data.replace(b'"need dictionary"', b'"no dictionary"')
    yield "wrong literal", extract(altered, folder, cc, flags)[1]


def check(work, label, kind, tree):
    name = "Zlib.Zutil.z_errmsg" if kind in {"table", "wrong literal"} else {"reference": "original", "lean": "standalone"}[label]
    check_declarations(work, label, MODULE, MODULE, [name], [tree], expect_mismatch=kind.startswith("wrong"))


def main():
    subprocess.run(["lake", "build", "--wfail", MODULE], cwd=ROOT, check=True)
    subprocess.run(["lake", "env", "leanchecker", "--fresh", MODULE], cwd=ROOT, check=True)
    with tempfile.TemporaryDirectory(prefix="zlib-source-zerror-") as tmp:
        work = Path(tmp)
        inputs = prepare_inputs(work, pinned=True)
        for label in ("reference", "lean"):
            folder = work / label
            for kind, tree in variants((folder / "zutil.c").read_bytes(), folder, inputs.compiler, inputs.flags):
                check(work, label, kind, tree)
                print(f"{label}/zutil.c zError: {kind} {'rejected' if kind.startswith('wrong') else 'checked'}")


if __name__ == "__main__":
    main()
