"""Check both ordered length reads and the alias-sensitive writebacks of uncompress2_z."""
import json
import subprocess
import tempfile
from pathlib import Path

from archive import prepare_inputs
from reference import ROOT
from source_bounds import local_name, require
from source_compress_lengths import check_suite, descendants, direct_call, tree, version_literal
from source_length_guards import MODULE as GUARD_MODULE, ctype, definition, expr, prefix, span

MODULE = "Lean2C.OriginalUncompressLengths"


def sections(data, folder, cfg, generated):
    body, scope = definition(data, folder, cfg.compiler, cfg.flags, "uncompress2_z")
    if generated:
        gate = body[4]
        require(gate["kind"] == "IfStmt" and len(body) == 5, "missing accepted body")
        accepted = gate["inner"][2]["inner"]
        dispatch = accepted[-1]
        require(dispatch["kind"] == "IfStmt", "missing initialization dispatch")
        success = dispatch["inner"][2]["inner"]
    else:
        require(body[4]["kind"] == "IfStmt", "missing original argument guard")
        accepted = body[5:]
        success = accepted
    loop, = [n for n in success if n["kind"] == "DoStmt"]
    tail = success[success.index(loop)+1:]
    first, second, *writeback = tail[:6 if generated else 4]
    cleanup = tail[6 if generated else 4]
    stream, = direct_call(cleanup, "inflateEnd")
    while stream["kind"] == "ParenExpr":
        stream, = stream["inner"]
    obj, = stream["inner"]
    stack, = body[0]["inner"]
    require(stream["kind"] == "UnaryOperator" and stream["opcode"] == "&" and obj["kind"] == "DeclRefExpr"
            and obj["referencedDecl"]["id"] == stack["id"], "cleanup of different stream")
    for node in [*body[:4], *accepted[:9], *success[:success.index(loop)]]:
        if node["kind"] == "DeclStmt":
            for var in node["inner"]:
                if var["name"] in {"stream", "left", "len", "len_1", "left_1", "err", "err_1", "max"}:
                    scope[var["id"]] = (local_name(var), ctype(var))
    return accepted, success, loop, scope, first, second, writeback, cleanup, tail


def extract(data, folder, cfg, generated):
    accepted, _, _, scope, first, second, writeback, cleanup, tail = sections(data, folder, cfg, generated)
    prefix = accepted[:2]
    if generated:
        for node in prefix:
            var, = node["inner"]
            scope.pop(var["id"], None)
    reads = tree(prefix, scope)
    counts = tree([first, second], scope)
    updates = tree(writeback, scope)
    length_ids = {id_ for id_, (name, _) in scope.items() if name in {'"sourceLen"', '"destLen"'}}
    def uses(nodes):
        return [n["id"] for st in nodes for n in descendants(st)
                if n["kind"] == "DeclRefExpr" and n["referencedDecl"]["id"] in length_ids]
    require(uses(accepted) == uses(prefix + writeback), "unaccounted length-pointer use")
    dest = tree(accepted[2:3], scope)
    exit_code = tree(tail[tail.index(cleanup)+1:], scope)
    return (reads, counts, updates, dest, exit_code), writeback


def cases(folder, cfg, label):
    generated = label == "lean"
    data = (folder / "uncompr.c").read_bytes()
    terms, stores = extract(data, folder, cfg, generated)
    names = [name + (" true" if generated else " false") for name in ("readLengths", "unusedCounts", "writeLengths", "selectDest", "returnResult")]
    for name, term in zip(names, terms, strict=True):
        yield name, term, False
    # Move a complete read/modify/write of one cell before the other.
    # This mutant differs even when both parameter types and writes are valid.
    mid = len(stores) // 2
    begin, _ = span(stores[0])
    next_begin, _ = span(stores[mid])
    _, last = span(stores[-1])
    require(data[last:last+1] == b";", "missing final semicolon")
    mutant = data[:begin] + data[next_begin:last+1] + b"\n" + data[begin:next_begin] + data[last+1:]
    yield names[2], extract(mutant, folder, cfg, generated)[0][2], True
    if generated:
        # Hoist the load of *destLen above the first store. When the cells
        # alias this changes the value, even though the two stores stay in order.
        store, read = stores[1:3]
        before, _ = span(store)
        start, end = span(read)
        require(data[end-1:end] == b";", "missing declaration terminator")
        stale = data[:before] + data[start:end] + b"\n" + data[before:start] + data[end:]
        yield names[2], extract(stale, folder, cfg, generated)[0][2], True


LOOP_MODULE = "Lean2C.OriginalUncompressLoop"


def extract_loop(data, folder, cfg, generated):
    _, success, loop, scope, *_ = sections(data, folder, cfg, generated)
    entry = success[2:success.index(loop)] if generated else []
    if generated:
        require(len(entry) == 6, "missing saved loop registers")
        for decl in entry[:3]:
            var, = decl["inner"]
            scope.pop(var["id"])
    for var in descendants(loop):
        if var["kind"] == "DeclRefExpr" and var["referencedDecl"]["name"] == "max":
            # Lookup by declaration identity, also checked against the top-level prelude below.
            require(var["referencedDecl"]["id"] in scope, "unexpected maximum declaration")
    initial = tree(entry, scope)
    block, test = loop["inner"]
    pre_out, pre_in, call, *copies = block["inner"]
    err_name = "err_2" if generated else "err"
    if generated:
        err, = call["inner"]
        require(call["kind"] == "DeclStmt" and err["kind"] == "VarDecl" and err["init"] == "c"
                and ctype(err) == ".i32" and err["name"] == err_name, "unexpected call result")
        fn, = err["inner"]
        scope[err["id"]] = (local_name(err), ctype(err))
    else:
        err, fn = call["inner"]
        require(call["kind"] == "BinaryOperator" and call["opcode"] == "=" and err["kind"] == "DeclRefExpr"
                and scope.get(err["referencedDecl"]["id"]) == ('"err"', ".i32"), "wrong assignment of inflate result")
    args = direct_call(fn, "inflate")
    stream, how = args
    while stream["kind"] == "ParenExpr":
        stream, = stream["inner"]
    ref, = stream["inner"]
    require(stream["kind"] == "UnaryOperator" and stream["opcode"] == "&" and ref["kind"] == "DeclRefExpr"
            and scope.get(ref["referencedDecl"]["id"]) == ('"stream"', '(.named "z_stream")'), "wrong inflate stream")
    return [tree([pre_out], scope.copy()), tree([pre_in], scope.copy()), expr(how, scope), expr(test, scope),
            initial, tree(copies, scope)], how


def loop_cases(folder, cfg, label):
    data = (folder / "uncompr.c").read_bytes()
    generated = label == "lean"
    flag = "true" if generated else "false"
    trees, how = extract_loop(data, folder, cfg, generated)
    names = [f"refillCode {flag} false", f"refillCode {flag} true", "flush", f"loopTest {flag}",
             f"entryLocals {flag}", f"saveResult {flag}"]
    for name, term in zip(names, trees, strict=True):
        yield name, term, False
    a, b = span(how)
    changed = data[:a] + b"4" + data[b:]
    yield names[2], extract_loop(changed, folder, cfg, generated)[0][2], True


INIT_MODULE = "Lean2C.OriginalUncompressInit"


def init_cases(folder, cfg, label):
    data = (folder / "uncompr.c").read_bytes()
    generated = label == "lean"
    accepted, success, loop, scope, *_ = sections(data, folder, cfg, generated)
    init = accepted[8]
    dispatch = accepted[9]
    require(dispatch["kind"] == "IfStmt", "missing init return check")
    if generated:
        require(len(accepted) == 10 and init["kind"] == "DeclStmt" and success.index(loop) == 8, "init control flow")
        err, = init["inner"]
        require(scope[err["id"]] == ('"err"', ".i32") and err["init"] == "c", "wrong init destination")
        fn, = err["inner"]
        cond, failure, _ = dispatch["inner"]
        fail_result, = failure["inner"]
        outputs = success[:2]
    else:
        require(init["kind"] == "BinaryOperator" and init["opcode"] == "=" and success.index(loop) == 12,
                "init control flow")
        err, fn = init["inner"]
        require(scope[err["referencedDecl"]["id"]] == ('"err"', ".i32"), "wrong init destination")
        cond, fail_result = dispatch["inner"]
        outputs = accepted[10:12]
    stream, version, size = direct_call(fn, "inflateInit_")
    while stream["kind"] == "ParenExpr":
        stream, = stream["inner"]
    obj, = stream["inner"]
    require(stream["kind"] == "UnaryOperator" and stream["opcode"] == "&"
            and obj["kind"] == "DeclRefExpr" and scope[obj["referencedDecl"]["id"]] ==
            ('"stream"', '(.named "z_stream")'), "wrong init stream")
    arg = f"({json.dumps(version_literal(version))}, {expr(size, scope)})"
    fail = tree([{"kind": "IfStmt", "inner": [cond, fail_result]}], scope)
    flag = "true" if generated else "false"
    yield "inputFields " + flag, tree(accepted[3:8], scope), False
    yield "outputFields " + flag, tree(outputs, scope), False
    yield "initArgs " + flag, arg, False
    yield "initCheck", fail, False


def main():
    modules = ["Lean2C.OriginalUncompressReturn"]
    subprocess.run(["lake", "build", "--wfail", *modules], cwd=ROOT, check=True)
    for module in modules:
        subprocess.run(["lake", "env", "leanchecker", "--fresh", module], cwd=ROOT, check=True)
    with tempfile.TemporaryDirectory(prefix="zlib-uncompress-lengths-") as tmp:
        work = Path(tmp)
        cfg = prepare_inputs(work, pinned=True)
        for label in ("reference", "lean"):
            folder = work / label
            generated = label == "lean"
            guard = prefix((folder / "uncompr.c").read_bytes(), folder, cfg.compiler, cfg.flags, "uncompress2_z", generated)[0]
            check_suite(work, label, GUARD_MODULE, [("standaloneUncompress" if generated else "originalUncompress", guard, False)])
            check_suite(work, label, INIT_MODULE, init_cases(folder, cfg, label))
            check_suite(work, label, MODULE, cases(folder, cfg, label))
            check_suite(work, label, LOOP_MODULE, loop_cases(work / label, cfg, label))


if __name__ == "__main__":
    main()
