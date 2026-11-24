"""Check the source blocks of the pinned compress2_z wrapper against its Lean execution."""
import json
from pathlib import Path
import subprocess
import tempfile

from archive import prepare_inputs
from reference import ROOT
from source_bounds import check_declarations, local_name, require
from source_length_guards import MODULE as GUARD_MODULE, ctype, definition, expr, prefix, span, statement

MODULE = "Lean2C.OriginalCompressLengths"


def descendants(node):
    yield node
    for child in node.get("inner", []):
        yield from descendants(child)


def direct_call(node, name):
    require(node["kind"] == "CallExpr", f"expected {name} call")
    decay, *args = node["inner"]
    require(decay["kind"] == "ImplicitCastExpr" and decay["castKind"] == "FunctionToPointerDecay",
            f"expected direct {name} call")
    ref, = decay["inner"]
    decl = ref["referencedDecl"]
    require(ref["kind"] == "DeclRefExpr" and decl["kind"] == "FunctionDecl" and decl["name"] == name,
            f"unexpected callee in {name} position")
    return args


def tree(nodes, scope):
    return "[" + ", ".join(statement(n, scope) for n in nodes) + "]"


def regions(data, directory, cc, flags, generated):
    body, scope = definition(data, directory, cc, flags, "compress2_z")
    names = ("strm",) if generated else ("stream", "left", "err")
    for decl in body:
        if decl["kind"] != "DeclStmt":
            break
        var, = decl["inner"]
        if var["name"] in names:
            scope[var["id"]] = (local_name(var), ctype(var))
    stream, = [v["inner"][0] for v in body if v["kind"] == "DeclStmt" and v["inner"][0]["name"] == names[0]]
    if generated:
        require(len(body) == 5, "unexpected top-level wrapper statements")
        *_, gate = body
        require(gate["kind"] == "IfStmt" and gate["inner"][2]["kind"] == "CompoundStmt", "missing accepted body")
        accepted = gate["inner"][2]["inner"]
        *_, init, dispatch = accepted
        require(init["kind"] == "DeclStmt" and dispatch["kind"] == "IfStmt" and len(dispatch["inner"]) == 3,
                "missing initialization dispatch")
        err, = init["inner"]
        direct_call(err["inner"][0], "deflateInit_")
        scope[err["id"]] = (local_name(err), ctype(err))
        cond, error, success = dispatch["inner"]
        refusal, = error["inner"]
        require(success["kind"] == "CompoundStmt", "missing initialized body")
        initialized = success["inner"]
    else:
        require(body[4]["kind"] == "IfStmt", "missing argument check")
        accepted = body[5:]
        dispatch, = [n for n in accepted if n["kind"] == "IfStmt"]
        i = accepted.index(dispatch)
        init = accepted[i-1]
        require(init["kind"] == "BinaryOperator" and init["opcode"] == "=", "missing initialization")
        require(init["inner"][0]["referencedDecl"]["id"] in scope and
                init["inner"][0]["referencedDecl"]["name"] == "err", "wrong initialization result")
        direct_call(init["inner"][1], "deflateInit_")
        cond, refusal = dispatch["inner"]
        initialized = accepted[i+1:]

    start = accepted[:2]
    loop, = [n for n in initialized if n["kind"] == "DoStmt"]
    tail = initialized[initialized.index(loop)+1:]
    if generated:
        saved, *tail = tail
        require(saved["kind"] == "BinaryOperator" and saved["opcode"] == "="
                and saved["inner"][0]["referencedDecl"]["id"] == err["id"], "missing final err assignment")
        loop_err, = [n["inner"][0] for n in initialized if n["kind"] == "DeclStmt" and n["inner"][0]["name"] == "s"]
        require(saved["inner"][1]["kind"] == "ImplicitCastExpr" and saved["inner"][1]["castKind"] == "LValueToRValue"
                and saved["inner"][1]["inner"][0]["referencedDecl"]["id"] == loop_err["id"], "wrong loop result")
    *finish, end_call, ret = tail
    arg, = direct_call(end_call, "deflateEnd")
    while arg["kind"] == "ParenExpr":
        arg, = arg["inner"]
    require(arg["kind"] == "UnaryOperator" and arg["opcode"] == "&"
            and arg["inner"][0]["referencedDecl"]["id"] == stream["id"], "cleanup of different stream")
    require(ret["kind"] == refusal["kind"] == "ReturnStmt", "missing error or final return")

    # The guard is checked separately. Every use of the length pointer after
    # acceptance must be in one of the two checked statement sequences.
    param_id, = [key for key, (name, _) in scope.items() if name == '"destLen"']
    def length_uses(nodes):
        return [n["id"] for st in nodes for n in descendants(st)
                if n["kind"] == "DeclRefExpr" and n["referencedDecl"]["id"] == param_id]
    require(length_uses(accepted) == length_uses(start + finish), "unaccounted use of destLen")
    init_branch = {"kind": "IfStmt", "inner": [cond, refusal]}
    return scope, body, accepted, initialized, start, finish, ret, init_branch, loop


def extract(data, directory, cc, flags, generated):
    scope, _, _, _, start, finish, ret, init_branch, _ = regions(data, directory, cc, flags, generated)
    return [tree(start, scope), tree(finish, scope), tree([ret], scope), tree([init_branch], scope)], start, finish


def cases(directory, inputs, label):
    generated = label == "lean"
    data = (directory / "compress.c").read_bytes()
    def parse(data):
        return extract(data, directory, inputs.compiler, inputs.flags, generated)
    trees, start, finish = parse(data)
    prefix = "standalone" if generated else "original"
    names = [prefix + "Start", prefix + "Writeback", "resultCode", "initResult"]
    for name, parsed in zip(names, trees, strict=True):
        yield name, parsed, False
    # Store one instead of zero, then reverse the pointer difference. Both
    # variants are well-typed on the target and go through the same importer.
    value = start[1]["inner"][1]
    lo, hi = span(value)
    zero = b"1UL" if generated else b"1"
    yield names[0], parse(data[:lo] + zero + data[hi:])[0][0], True
    diff, = [n for st in finish for n in descendants(st) if n["kind"] == "BinaryOperator" and n["opcode"] == "-"]
    lhs, rhs = diff["inner"]
    left, mid = span(lhs)
    right, last = span(rhs)
    reversed_diff = data[:left] + data[right:last] + b" - " + data[left:mid] + data[last:]
    yield names[1], parse(reversed_diff)[0][1], True


LOOP_MODULE = "Lean2C.OriginalCompressLoop"


def loop_parts(data, directory, cfg, generated):
    scope, body, accepted, initialized, _, _, _, _, loop = regions(data, directory, cfg.compiler, cfg.flags, generated)
    for statement_ in [*body, *accepted, *initialized[:initialized.index(loop)]]:
        if statement_["kind"] != "DeclStmt":
            continue
        for local in statement_["inner"]:
            if local.get("name") in {"max", "left", "s", "s_1", "s_2"}:
                scope[local["id"]] = (local_name(local), ctype(local))
    block, cond = loop["inner"]
    require(block["kind"] == "CompoundStmt", "expected loop compound statement")
    nodes = block["inner"]
    if generated:
        restore_left, restore_in, out_decl, out_read, out_if, in_decl, in_read, in_if, call, *save = nodes
        output = [out_decl, out_read, out_if]
        input_ = [in_decl, in_read, in_if]
        restore = [restore_left, restore_in]
        err, = call["inner"]
        require(call["kind"] == "DeclStmt" and err["kind"] == "VarDecl" and err["init"] == "c"
                and ctype(err) == ".i32" and err["name"] == "err_1", "invalid deflate result local")
        fn, = err["inner"]
        scope[err["id"]] = (local_name(err), ctype(err))
    else:
        out_if, in_if, call = nodes
        output, input_, restore, save = [out_if], [in_if], [], []
        require(call["kind"] == "BinaryOperator" and call["opcode"] == "="
                and scope.get(call["inner"][0]["referencedDecl"]["id"]) == ('"err"', ".i32"),
                "unexpected call result assignment")
        fn = call["inner"][1]
    stream, flush = direct_call(fn, "deflate")
    while stream["kind"] == "ParenExpr":
        stream, = stream["inner"]
    require(ctype(fn) == ".i32" and stream["kind"] == "UnaryOperator" and stream["opcode"] == "&",
            "expected the address of the live stream")
    local, = stream["inner"]
    require(local["kind"] == "DeclRefExpr" and scope.get(local["referencedDecl"]["id"]) ==
            (('"strm"' if generated else '"stream"'), '(.named "z_stream")'), "wrong deflate stream")
    index = initialized.index(loop)
    entry = initialized[4:index]
    pre_scope = {key: pair for key, pair in scope.items() if pair[0] not in {'"s"', '"s_1"', '"s_2"'}}
    copy_result = initialized[index+1:index+2] if generated else []
    return [tree(restore, scope), tree(output, scope), tree(input_, scope), expr(flush, scope),
            tree(save, scope), expr(cond, scope), tree(entry, pre_scope), tree(copy_result, scope)], out_if, in_if


def loop_cases(directory, inputs, label):
    data = (directory / "compress.c").read_bytes()
    generated = label == "lean"
    def parse(data):
        return loop_parts(data, directory, inputs, generated)
    trees, out_if, in_if = parse(data)
    flag = "true" if generated else "false"
    names = [f"restoreLocals {flag}", f"refillCode {flag} false", f"refillCode {flag} true",
             f"flushArgument {flag}", f"saveLocals {flag}", f"whileCondition {flag}", f"entryLocals {flag}", f"copyResult {flag}"]
    for name, parsed in zip(names, trees, strict=True):
        yield name, parsed, False
    # Switch the target stream field while preserving the C lvalue type.
    for i, (branch, field, replacement) in enumerate(((out_if, b"avail_out", b"avail_in"),
                                                      (in_if, b"avail_in", b"avail_out")), 1):
        member, = [n["inner"][0] for n in descendants(branch) if n["kind"] == "BinaryOperator"
                   and n["opcode"] == "=" and n["inner"][0]["kind"] == "MemberExpr"]
        _, end = span(member)
        require(data[end-len(field):end] == field, "unexpected refill field")
        changed = data[:end-len(field)] + replacement + data[end:]
        yield names[i], parse(changed)[0][i], True


INIT_MODULE = "Lean2C.OriginalCompressInit"


def version_literal(version):
    require(version["kind"] == "ImplicitCastExpr" and version["castKind"] == "NoOp"
            and version["type"]["qualType"] == "const char *", "unexpected version pointer")
    decay, = version["inner"]
    literal, = decay["inner"]
    require(decay["kind"] == "ImplicitCastExpr" and decay["castKind"] == "ArrayToPointerDecay"
            and literal["kind"] == "StringLiteral" and not literal.get("inner"), "expected version literal")
    version_text = json.loads(literal["value"])
    require(all(ch.isascii() and (ch.isalnum() or ch in ".-") for ch in version_text)
            and literal["type"]["qualType"] == f"char[{len(version_text)+1}]", "unsupported literal spelling")
    return version_text


def init_parts(data, directory, cfg, generated):
    scope, _, accepted, initialized, _, _, _, _, loop = regions(data, directory, cfg.compiler, cfg.flags, generated)
    init = accepted[5]
    if generated:
        require(len(accepted) == 7 and len(initialized[:initialized.index(loop)]) == 10, "unexpected wrapper statement")
        fn = init["inner"][0]["inner"][0]
    else:
        require(accepted[6]["kind"] == "IfStmt" and len(initialized[:initialized.index(loop)]) == 4,
                "unexpected wrapper statement")
        fn = init["inner"][1]
    stream, level, version, size = direct_call(fn, "deflateInit_")
    while stream["kind"] == "ParenExpr":
        stream, = stream["inner"]
    require(stream["kind"] == "UnaryOperator" and stream["opcode"] == "&", "expected the stream address")
    ref, = stream["inner"]
    require(ref["kind"] == "DeclRefExpr" and scope.get(ref["referencedDecl"]["id"]) ==
            (('"strm"' if generated else '"stream"'), '(.named "z_stream")'), "wrong initialization stream")
    version_text = version_literal(version)
    args = f"({expr(level, scope)}, {json.dumps(version_text)}, {expr(size, scope)})"
    return [tree(accepted[2:5], scope), tree(initialized[:4], scope), args], initialized[1]


def init_cases(directory, inputs, label):
    generated = label == "lean"
    data = (directory / "compress.c").read_bytes()
    def parse(data):
        return init_parts(data, directory, inputs, generated)
    trees, clear = parse(data)
    names = [f"{fn} {'true' if generated else 'false'}" for fn in ("allocators", "buffers", "initArgs")]
    for name, parsed in zip(names, trees, strict=True):
        yield name, parsed, False
    lo, hi = span(clear["inner"][1])
    yield names[1], parse(data[:lo] + (b"1U" if generated else b"1") + data[hi:])[0][1], True


def check_suite(work, label, module, entries):
    original, mutants = [], []
    for name, parsed, mismatch in entries:
        (mutants if mismatch else original).append((name, parsed))
    names, trees = zip(*original)
    check_declarations(work, label, module, module, names, trees)
    for name, parsed in mutants:
        check_declarations(work, label, module, module, [name], [parsed], expect_mismatch=True)
    print(f"{label} {module}: {len(original)} source fragments checked, {len(mutants)} mutations rejected", flush=True)


def main():
    wrapper = "Lean2C.OriginalCompress"
    subprocess.run(["lake", "build", "--wfail", wrapper], cwd=ROOT, check=True)
    subprocess.run(["lake", "env", "leanchecker", "--fresh", wrapper], cwd=ROOT, check=True)
    with tempfile.TemporaryDirectory(prefix="zlib-compress-lengths-") as tmp:
        work = Path(tmp)
        cfg = prepare_inputs(work, pinned=True)
        for label in ("reference", "lean"):
            folder = work / label
            generated = label == "lean"
            data = (folder / "compress.c").read_bytes()
            guard = prefix(data, folder, cfg.compiler, cfg.flags, "compress2_z", generated)[0]
            check_suite(work, label, GUARD_MODULE, [(("standalone" if generated else "original") + "Compress", guard, False)])
            for module, suite in ((MODULE, cases), (LOOP_MODULE, loop_cases), (INIT_MODULE, init_cases)):
                check_suite(work, label, module, suite(folder, cfg, label))


if __name__ == "__main__":
    main()
