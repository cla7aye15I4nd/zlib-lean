"""Check decoder register updates, match copies, callback guards, and code-length indices."""
from pathlib import Path
import subprocess
import tempfile
from typing import NamedTuple

from archive import prepare_inputs
from ast_compare import clang, function_body, location
from reference import ROOT
from source_bounds import require


# Expected LP64 member and register types. Clang preserves Bytef in pointer spellings.
BYTE_PTR = {"Bytef *", "unsigned char *"}
UINT = {"unsigned int"}
ULONG = {"unsigned long"}
MEMBERS = {"next_out": BYTE_PTR, "avail_out": UINT, "next_in": BYTE_PTR, "avail_in": UINT,
           "hold": ULONG, "bits": UINT}
REGISTERS = {"put": BYTE_PTR, "left": UINT, "next": BYTE_PTR, "have_": UINT,
             "hold": ULONG, "bits": UINT}
BACK_MODES = {"TYPE": 16191, "STORED": 16193, "TABLE": 16196, "LEN": 16200, "DONE": 16208, "BAD": 16209}


def walk(node):
    yield node
    for child in node.get("inner", []):
        yield from walk(child)


def read(node):
    if node.get("kind") == "ImplicitCastExpr" and node.get("castKind") == "LValueToRValue":
        node, = node["inner"]
    return node


def typed(node, allowed):
    ty = node["type"]
    require(ty.get("desugaredQualType", ty["qualType"]) in allowed, f"unexpected type {ty}")


def variable(node):
    node = read(node)
    require(node.get("kind") == "DeclRefExpr", "expected a plain variable")
    return node["referencedDecl"]


def expression(node):
    while (node.get("kind") == "ParenExpr" or
           node.get("kind") in {"CStyleCastExpr", "ImplicitCastExpr"} and
           node.get("castKind") in {"NoOp", "LValueToRValue"}):
        node, = node["inner"]
    return node


def callback_cursor_sites(fn, reference, direct_cursor=None):
    """Check the local address and descriptor at each indirect infback call."""
    body = function_body(fn)
    stream, input_fn, input_desc, output_fn, output_desc = [p for p in fn["inner"] if p["kind"] == "ParmVarDecl"]
    cursor_name = "next" if reference else "cell"
    cursor, = [n for n in walk(body) if n.get("kind") == "VarDecl" and n["name"] == cursor_name]
    typed(cursor, BYTE_PTR)
    require("storageClass" not in cursor and "tls" not in cursor, "expected an automatic input cursor")
    parents = {child["id"]: parent for parent in walk(body) for child in parent.get("inner", []) if "id" in child}
    counts = [0, 0]
    fn_ids = (input_fn["id"], output_fn["id"])
    mutations = {}

    def cursor_address(arg):
        address = expression(arg)
        require(address.get("opcode") == "&", "expected the address of the input cursor")
        typed(address, {"unsigned char **"})
        local = expression(address["inner"][0])
        require(local.get("kind") == "DeclRefExpr" and variable(local)["id"] == cursor["id"], "wrong callback cursor")
        start = local["range"]["begin"]
        return start.get("spellingLoc", start)

    def indirect_cursor(arg):
        load = expression(arg)
        require(load.get("opcode") == "*", "expected access through the cursor address")
        return cursor_address(load["inner"][0])

    if direct_cursor:
        registers, = [n for n in walk(body) if n.get("kind") == "VarDecl" and n["name"] == "registers"]
        require(all(not (n.get("kind") == "MemberExpr" and not n["isArrow"] and n["name"] == "next"
                         and expression(n["inner"][0]).get("referencedDecl", {}).get("id") == registers["id"])
                    for n in walk(body)), "decoder cursor stored in a second register")
    if reference or direct_cursor:
        if reference:
            writes = [n for n in body["inner"] if n.get("opcode") == "=" and
                      expression(n["inner"][0]).get("referencedDecl", {}).get("id") == cursor["id"]]
            require(writes, "missing initial input cursor")
            field = expression(writes[0]["inner"][1])
        else:
            field = expression(cursor["inner"][0])
        require(field.get("name") == "next_in" and field["isArrow"] and
                variable(expression(field["inner"][0]))["id"] == stream["id"], "wrong callback cursor")
        stores = [n for n in walk(body) if n.get("opcode") == "=" and n["inner"][0].get("name") == "next_in"]
        require(stores, "missing final input cursor publication")
        final, value = stores[-1]["inner"]
        require(final["isArrow"] and variable(expression(final["inner"][0]))["id"] == stream["id"]
                and expression(value).get("referencedDecl", {}).get("id") == cursor["id"], "wrong callback cursor")
        last = location(expression(value)["range"]["end"])
        mutations["final cursor"] = (last, b"put" if reference else b"registers.put")
        field_pos = location(field["range"]["end"])
        mutations["initial cursor"] = (field_pos, b"next_out")

    for call in walk(body):
        if call.get("kind") != "CallExpr":
            continue
        callee, *args = call["inner"]
        ident = expression(callee).get("referencedDecl", {}).get("id")
        if ident not in fn_ids:
            continue
        output = ident == output_fn["id"]
        counts[int(output)] += 1
        desc = output_desc if output else input_desc
        require(variable(expression(args[0]))["id"] == desc["id"], "wrong callback descriptor")
        if not output:
            pos = cursor_address(args[1])
            mutations.setdefault("input cursor", (pos, b"put" if reference else b"registers.put" if direct_cursor else b"next"))
        if reference or direct_cursor:
            continue
        stmt = call
        while parents[stmt["id"]]["kind"] != "CompoundStmt":
            stmt = parents[stmt["id"]]
        siblings = parents[stmt["id"]]["inner"]
        i = next(k for k, sibling in enumerate(siblings) if sibling["id"] == stmt["id"])
        require(stmt["kind"] == "DeclStmt" and 0 < i < len(siblings) - 1, "missing callback boundary")
        result, = stmt["inner"]
        require(result["inner"][0]["id"] == call["id"], "expected a direct callback initializer")
        publish = expression(siblings[i - 1])
        require(publish.get("opcode") == "=", "cursor must be published before the call")
        target, source = publish["inner"]
        pos = indirect_cursor(target)
        if output:
            mutations.setdefault("output publication", (pos, b"next"))
        source = expression(source)
        require((source.get("kind") == "MemberExpr" and source["name"] == "next" and not source["isArrow"])
                or (source.get("kind") == "DeclRefExpr" and variable(source)["name"] == "next"),
                "expected the decoder input cursor")
        reload = siblings[i + 1]
        require(reload["kind"] == "DeclStmt", "cursor must be read after the call")
        saved, = reload["inner"]
        typed(saved, BYTE_PTR)
        pos = indirect_cursor(saved["inner"][0])
        if output:
            mutations.setdefault("output reload", (pos, b"next"))
    require(counts == [15, 4], f"unexpected inflateBack callback sites {counts}")
    for fn_id, count in zip(fn_ids, counts):
        uses = sum(n.get("referencedDecl", {}).get("id") == fn_id for n in walk(body))
        require(uses == count, "unexpected additional use of callback parameter")
    return [(pos["offset"], pos["tokLen"], replacement) for pos, replacement in mutations.values()]


class StoredCase(NamedTuple):
    copy: tuple
    cursor_span: tuple
    header: tuple
    shift_span: tuple


def back_terms(fn, state, locals_by_id, registers):
    """Resolve typed decoder expressions to registers, parameters and fields."""
    body = function_body(fn)
    stream, in_fn, in_desc, out_fn, out_desc = [n for n in fn["inner"] if n["kind"] == "ParmVarDecl"]
    params = {n["id"]: key for n, key in zip((in_fn, in_desc, out_fn, out_desc),
                                             ("input", "inDesc", "output", "outDesc"))}
    label, = [n for n in walk(body) if n.get("kind") == "LabelStmt" and n["name"] == "inf_leave"]

    def term(node):
        kind = node["kind"]
        children = node.get("inner", [])
        if kind == "ParenExpr":
            return term(children[0])
        if kind == "CStyleCastExpr" and node["castKind"] == "IntegralCast":
            child, = children
            ty = node["type"]["qualType"]
            if ty == "unsigned int" and expression(child)["kind"] == "IntegerLiteral":
                typed(child, {"int"})
                return term(child)
            typed(child, ULONG if ty == "unsigned int" else {"unsigned char"})
            require(ty in UINT | ULONG, "unexpected stored header cast")
            return (ty, term(child))
        if kind in {"ImplicitCastExpr", "CStyleCastExpr"}:
            child, = children
            cast = node["castKind"]
            if cast == "NullToPointer":
                typed(node, BYTE_PTR)
                require(term(child) == 0, "nonzero null pointer constant")
                return "null"
            if cast == "IntegralCast":
                src = child["type"]
                src = src.get("desugaredQualType", src["qualType"])
                dst = node["type"]
                dst = dst.get("desugaredQualType", dst["qualType"])
                require((src, dst) == ("unsigned int", "unsigned long") or
                        dst in UINT | ULONG and expression(child)["kind"] == "IntegerLiteral" or
                        dst == "inflate_mode" and src in {"int", "unsigned int"},
                        "unexpected stored-block integer conversion")
            elif cast == "BitCast":
                typed(child, BYTE_PTR)
                typed(node, {"void *", "const void *"})
            else:
                require(cast in {"LValueToRValue", "FunctionToPointerDecay", "NoOp", "ArrayToPointerDecay"},
                        "unexpected stored-block cast")
            return term(child)
        if kind == "IntegerLiteral":
            typed(node, {"int"} | UINT | ULONG)
            return int(node["value"])
        if kind == "StringLiteral":
            return node["value"]
        if kind == "MemberExpr" and node["isArrow"]:
            field = node["name"]
            base = variable(expression(children[0]))
            if base["id"] == stream["id"]:
                require(field in {"msg", "next_in", "avail_in"}, "unexpected input stream member")
                typed(node, {"char *"} if field == "msg" else MEMBERS[field])
                return ("stream", field)
            require(base["id"] == state["id"], "wrong stored-block state")
            typed(node, BYTE_PTR if field == "window" else {"inflate_mode"} if field == "mode" else UINT)
            return ("state", field)
        if kind in ("DeclRefExpr", "MemberExpr"):
            reg = decoder_register(node, locals_by_id, registers)
            if reg in ("next", "put", "have", "have_", "left", "copy", "ret", "bits", "hold"):
                typed(node, BYTE_PTR if reg in ("next", "put") else {"int"} if reg == "ret" else ULONG if reg == "hold" else UINT)
                return "have_" if reg == "have" else reg
            decl = variable(node)
            if decl["kind"] == "EnumConstantDecl":
                return BACK_MODES[decl["name"]]
            if decl["id"] in params:
                return params[decl["id"]]
            require(decl["kind"] == "FunctionDecl" and decl["name"] == "memcpy", "unknown stored-loop operand")
            typed(decl, {"void *(void *, const void *, unsigned long)"})
            return "memcpy"
        if kind == "CompoundStmt":
            return tuple(map(term, children))
        if kind == "DoStmt":
            block, test = children
            require(term(test) == 0 and len(block["inner"]) == 1, "unexpected stored-loop macro wrapper")
            return term(block["inner"][0])
        if kind == "GotoStmt":
            require(node["targetLabelDeclId"] == label["declId"], "wrong stored-loop callback exit")
            return "leave"
        if kind == "CallExpr":
            return tuple(map(term, children))
        if kind == "UnaryOperator" and node["opcode"] in {"++", "--"}:
            require(node["isPostfix"], "expected a postfix update in PULLBYTE")
        if kind == "BreakStmt":
            return "break"
        if kind == "IfStmt":
            guard, yes = children
            return ("if", term(guard), term(yes))
        require(kind in ("BinaryOperator", "UnaryOperator", "CompoundAssignOperator"),
                f"unexpected stored-loop operation {kind}")
        return (node["opcode"], *map(term, children))

    return term


def back_finish(fn, term):
    """Check all statements from the shared inf_leave label through return."""
    body = function_body(fn)
    parent, = [n for n in walk(body) if n.get("kind") == "CompoundStmt" and any(
        child.get("kind") == "LabelStmt" and child["name"] == "inf_leave" for child in n.get("inner", []))]
    nodes = parent["inner"]
    i = next(i for i, n in enumerate(nodes) if n.get("kind") == "LabelStmt" and n["name"] == "inf_leave")
    first, = nodes[i]["inner"]
    branch, cursor, count, ret = ([] if first["kind"] == "NullStmt" else [first]) + nodes[i + 1:]
    require(branch["kind"] == "IfStmt" and len(branch["inner"]) == 2, "wrong final output branch")
    test, outer = branch["inner"]
    inner, = outer["inner"]
    require(inner["kind"] == "IfStmt" and len(inner["inner"]) == 2, "wrong final output status test")
    cond, assign = inner["inner"]
    if assign["kind"] == "CompoundStmt":
        assign, = assign["inner"]
    size = ("state", "wsize")
    send = ("output", "outDesc", ("state", "window"), ("-", size, "left"))
    require(term(test) == ("<", "left", size) and term(cond) == ("&&", send, ("==", "ret", 1))
            and term(assign) == ("=", "ret", ("-", 5)), "wrong final output invocation or status")
    require(term(cursor) == ("=", ("stream", "next_in"), "next")
            and term(count) == ("=", ("stream", "avail_in"), "have_")
            and ret["kind"] == "ReturnStmt" and term(ret["inner"][0]) == "ret", "wrong final stream writeback")
    field = next(n for n in walk(cond) if n.get("name") == "wsize")
    pos = location(field["range"]["end"])
    return pos["offset"], pos["tokLen"]


def back_stored_case(fn, term, arm):
    """Import the stored header and copy from the selected switch arm in each decoder."""
    body = function_body(fn)

    def field(name):
        return ("state", name)

    zero_in, zero_out = ("==", "have_", 0), ("==", "left", 0)
    stop = (("=", "ret", ("-", 5)), "leave")
    pull = ("if", zero_in, (("=", "have_", ("input", "inDesc", ("&", "next"))),
                            ("if", zero_in, (("=", "next", "null"), *stop))))
    room = ("if", zero_out, (("=", "put", field("window")), ("=", "left", field("wsize")),
                             ("=", field("whave"), "left"), ("if", ("output", "outDesc", "put", "left"), stop)))
    names = ("have_", "left")
    clamp = tuple(("if", (">", "copy", n), ("=", "copy", n)) for n in names)
    loops = [n for n in walk(body) if n.get("kind") == "WhileStmt" and
             n["inner"][0].get("opcode") == "!=" and expression(n["inner"][0]["inner"][0]).get("name") == "length" and
             any(v.get("referencedDecl", {}).get("name") == "memcpy" for v in walk(n["inner"][1]))]
    require(len(loops) == 1, "expected one callback stored-block copy loop")
    guard, block = loops[0]["inner"]
    require(term(guard) == ("!=", field("length"), 0), "wrong stored-block loop test")
    stmts = block["inner"]
    require(len(stmts) == 11, "unexpected callback stored-block operation count")
    values = tuple(map(term, stmts))
    require(values[:5] == (("=", "copy", field("length")), pull, room, *clamp), "wrong stored-block callback order or clamp")
    require(values[6:] == (("-=", "have_", "copy"), ("+=", "next", "copy"), ("-=", "left", "copy"),
                           ("+=", "put", "copy"), ("-=", field("length"), "copy")), "wrong stored-block cursor update")
    name, dst, src, size = values[5]
    require(name == "memcpy" and dst in ("next", "put") and src in ("next", "put") and size == "copy",
            "wrong stored-block copy")
    cursor = stmts[5]["inner"][2]["range"]["end"]
    pos = cursor.get("spellingLoc", cursor)
    cursor_span = pos["offset"], pos["tokLen"]

    def statements(nodes):
        result = []
        for node in nodes:
            if node["kind"] == "NullStmt":
                continue
            if node["kind"] == "DoStmt":
                group, guard = node["inner"]
                require(term(guard) == 0 and group["kind"] == "CompoundStmt", "unexpected stored header macro")
                result.extend(statements(group["inner"]))
            else:
                result.append(node)
        return result

    align, discard, need, branch, *tail = statements(arm)
    require((term(align), term(discard)) == ((">>=", "hold", ("&", "bits", 7)), ("-=", "bits", ("&", "bits", 7))),
            "wrong stored block byte alignment")
    require(need["kind"] == "WhileStmt", "expected stored header refill")
    test, read_byte = need["inner"]
    op, bits, width = term(test)
    require((op, bits) == ("<", "bits") and isinstance(width, int), "wrong stored header refill guard")
    block = read_byte
    if read_byte["kind"] == "DoStmt":
        block, test = read_byte["inner"]
        require(term(test) == 0, "unexpected input byte repetition")
    require(block["kind"] == "CompoundStmt", "unexpected refill body")
    ops = tuple(map(term, statements(block["inner"])))
    require(len(ops) == 4 and ops[:3] == (pull, ("--", "have_"),
            ("+=", "hold", ("<<", ("unsigned long", ("*", ("++", "next"))), "bits")))
            and ops[3][:2] == ("+=", "bits"), "wrong stored header input byte")
    increment = ops[3][2]
    require(branch["kind"] == "IfStmt", "expected stored length complement check")
    test, bad, *good = branch["inner"]
    cmp, lower, upper = term(test)
    op, hold, mask = lower
    xor, shifted, complement = upper
    shr, other_hold, shift = shifted
    require((cmp, op, hold, xor, shr, other_hold) == ("!=", "&", "hold", "^", ">>", "hold"), "wrong stored header comparison")
    shift_token, = [node for node in walk(test) if node.get("opcode") == ">>"]
    literal, = [node for node in walk(shift_token["inner"][1]) if node.get("kind") == "IntegerLiteral"]
    loc = location(literal["range"]["end"])
    message, mode, *stop = [term(node) for node in bad["inner"]]
    require(message == ("=", ("stream", "msg"), '"invalid stored block lengths"') and mode[:2] == ("=", field("mode")),
            "wrong invalid stored header path")
    if good:
        require(not stop and len(good) == len(tail) == 1 and term(tail[0]) == "break", "wrong generated stored control flow")
        tail = statements(good[0]["inner"])
    else:
        require(stop == ["break"] and term(tail[-1]) == "break", "wrong original stored control flow")
        tail = tail[:-1]
    save, zero_hold, zero_bits, copy, finish = tail
    assign, length, value = term(save)
    mask_op, cast, length_mask = value
    require((assign, length, mask_op, cast) == ("=", field("length"), "&", ("unsigned int", "hold")), "wrong stored length")
    require(term(zero_hold) == ("=", "hold", 0) and term(zero_bits) == ("=", "bits", 0)
            and copy["id"] == loops[0]["id"], "wrong stored copy entry")
    assign, target, next_mode = term(finish)
    require((assign, target) == ("=", field("mode")), "wrong stored block continuation")
    header = (width, mask, shift, complement, mode[2], length_mask, next_mode, increment)
    require(all(isinstance(n, int) and 0 <= n < 2**32 for n in header), "invalid stored header constants")
    return StoredCase((dst, src), cursor_span, header, (loc["offset"], loc["tokLen"]))


def bit_tests(body, state, bits, frame):
    """Read the guard at the loop header, resolving only fresh locals assigned on each visit."""
    guards = []
    for loop in walk(body):
        bindings = {}
        operands = []
        if loop.get("kind") == "WhileStmt":
            test = expression(loop["inner"][0])
        elif frame is not None and loop.get("kind") == "ForStmt" and not any(loop["inner"][:-1]):
            block = loop["inner"][-1]
            if block.get("kind") != "CompoundStmt":
                continue
            declared = set()
            test = None
            for stmt in block["inner"]:
                if stmt["kind"] == "DeclStmt":
                    var, = stmt["inner"]
                    declared.add(var["id"])
                    if var.get("init") == "c":
                        bindings[var["id"]], = var["inner"]
                        operands.append(bindings[var["id"]])
                elif stmt.get("opcode") == "=" and stmt["inner"][0].get("kind") == "DeclRefExpr":
                    lhs, rhs = stmt["inner"]
                    target = variable(lhs)["id"]
                    if target not in declared or target in bindings:
                        break
                    bindings[target] = rhs
                    operands.append(rhs)
                else:
                    if stmt["kind"] == "IfStmt" and len(stmt["inner"]) == 2:
                        neg, jump = stmt["inner"]
                        if neg.get("opcode") == "!" and jump["kind"] == "BreakStmt":
                            flag = expression(neg["inner"][0])
                            if flag.get("kind") == "DeclRefExpr":
                                value = bindings.get(variable(flag)["id"])
                                if value is not None:
                                    test = expression(value)
                    break
        else:
            continue
        if not test or test.get("opcode") != "<":
            continue
        left, right = map(expression, test["inner"])
        if right.get("kind") == "DeclRefExpr" and variable(right)["id"] in bindings:
            right = expression(bindings[variable(right)["id"]])
        if right.get("kind") != "MemberExpr" or not right["isArrow"]:
            continue
        base = expression(right["inner"][0])
        if base.get("kind") != "DeclRefExpr" or variable(base)["id"] != state["id"]:
            continue
        typed(left, UINT)
        typed(right, UINT)
        if bits is not None:
            if left.get("kind") != "DeclRefExpr" or variable(left)["id"] != bits["id"]:
                continue
        else:
            if left.get("kind") != "MemberExpr" or left["isArrow"] or left["name"] != "bits":
                continue
            allowed = {"DeclRefExpr", "MemberExpr", "ParenExpr", "ImplicitCastExpr", "CStyleCastExpr"}
            require(all((n["kind"] in allowed or n.get("opcode") == "<") and
                        "volatile" not in n["type"]["qualType"] for operand in operands for n in walk(operand)),
                    "unexpected operation before the generated loop guard")
            snapshot = variable(left["inner"][0])
            require(snapshot["id"] == frame["id"] or
                    (snapshot["id"] in bindings and variable(bindings[snapshot["id"]])["id"] == frame["id"]),
                    "bits must come from a fresh copy of the current registers")
        end = right["range"]["end"]
        guards.append((right["name"], end.get("spellingLoc", end)["offset"]))
    require(len(guards) == 2, f"expected two live decoder-state bit counts, found {len(guards)}")
    return guards


def length_appends(body, state, reference):
    """Map each typed lens[stream_field++] store to its index field and source token."""
    declarations = {n["id"]: n for n in walk(body) if n.get("kind") == "VarDecl"}
    appends = {}
    for stmt in walk(body):
        if stmt.get("kind") != "BinaryOperator" or stmt.get("opcode") != "=":
            continue
        lhs, rhs = stmt["inner"]
        if lhs.get("kind") != "ArraySubscriptExpr":
            continue
        array, index = lhs["inner"]
        index = expression(index)
        if index.get("opcode") != "++" or not index.get("isPostfix"):
            continue
        if array.get("castKind") != "ArrayToPointerDecay":
            continue
        member = expression(array["inner"][0])
        if member.get("kind") != "MemberExpr" or member["name"] != "lens":
            continue
        counter = expression(index["inner"][0])
        require(member["isArrow"] and counter.get("kind") == "MemberExpr" and counter["isArrow"],
                "expected fields of the decoder state")
        owner = variable(expression(member["inner"][0]))
        require(variable(expression(counter["inner"][0]))["id"] == owner["id"], "wrong index owner")
        if owner["id"] != state["id"]:
            alias = declarations[owner["id"]]
            require(not reference and alias.get("init") == "c"
                    and variable(expression(alias["inner"][0]))["id"] == state["id"],
                    "unrelated state in length store")
        typed(lhs, {"unsigned short"})
        typed(rhs, {"unsigned short"})
        typed(index, UINT)
        typed(counter, UINT)
        field = counter["name"]
        require(field.isascii() and field.isidentifier(), "invalid index field")
        end = counter["range"]["end"]
        appends[stmt["id"]] = (field, end.get("spellingLoc", end)["offset"])
    require(len(appends) == 2, f"expected two direct code-length appends, found {len(appends)}")
    return appends

def decoder_register(node, locals_by_id, registers):
    node = expression(node)
    if node["kind"] == "DeclRefExpr":
        return locals_by_id.get(variable(node)["id"])
    if registers and node["kind"] == "MemberExpr" and not node["isArrow"]:
        if variable(expression(node["inner"][0]))["id"] == registers["id"]:
            return node["name"]
    return None


def repeated_length(body, appends, locals_by_id, registers):
    """Import the unsigned decrement test and the one length store in its body."""
    loops = []
    for loop in walk(body):
        if loop.get("kind") != "WhileStmt":
            continue
        test, store = loop["inner"]
        if store.get("kind") == "CompoundStmt":
            items = store.get("inner", [])
            if len(items) != 1:
                continue
            store = items[0]
        if store.get("id") not in appends:
            continue
        test = expression(test)
        require(test.get("kind") == "UnaryOperator" and test.get("opcode") == "--", "expected a decrement test")
        typed(test, UINT)
        counter = decoder_register(test["inner"][0], locals_by_id, registers)
        require(counter in {"copy", "left", "bits"}, "unexpected repeat counter")
        rhs = expression(store["inner"][1])
        require(rhs.get("kind") == "CStyleCastExpr" and rhs.get("castKind") == "IntegralCast",
                "expected conversion of the repeated length to unsigned short")
        operand = expression(rhs["inner"][0])
        typed(operand, UINT)
        value = decoder_register(operand, locals_by_id, registers)
        require(value in {"len", "copy", "left"}, "unexpected repeat value")
        first, last = (location(test["range"][end]) for end in ("begin", "end"))
        last_value = location(operand["range"]["end"])
        fields = (counter, test["isPostfix"], appends[store["id"]][0], value)
        loops.append((fields, (first["offset"], last["offset"] + last["tokLen"]), last_value["offset"]))
    require(len(loops) == 1, f"expected one code-length repeat, found {len(loops)}")
    return loops[0]


def input_bytes(body, locals_by_id, registers, count):
    """Import the three consecutive PULLBYTE operations on the live decoder registers."""
    def register(node):
        return decoder_register(node, locals_by_id, registers)

    def unary(node, op, postfix, ty):
        node = expression(node)
        require(node["kind"] == "UnaryOperator" and node["opcode"] == op and node["isPostfix"] == postfix,
                f"expected {op} in the input-byte sequence")
        typed(node, ty)
        return expression(node["inner"][0])

    widths = []
    mutation = None
    for block in walk(body):
        if block.get("kind") != "CompoundStmt":
            continue
        stmts = block.get("inner", [])
        for index, store in enumerate(stmts):
            if store.get("opcode") != "+=" or register(store["inner"][0]) != "hold":
                continue
            require(0 < index < len(stmts) - 1, "missing input count or bit-count update")
            count_reg = unary(stmts[index - 1], "--", True, UINT)
            require(register(count_reg) == ("have_" if registers else "have"), "wrong input count")
            hold, shift = store["inner"]
            typed(hold, ULONG)
            shift = expression(shift)
            require(shift.get("opcode") == "<<", "expected the input byte shifted by the current bit count")
            typed(shift, ULONG)
            cast, bits = map(expression, shift["inner"])
            typed(cast, ULONG)
            require(cast["kind"] == "CStyleCastExpr" and cast["castKind"] == "IntegralCast",
                    "expected conversion of the byte to unsigned long")
            postinc = unary(cast["inner"][0], "*", False, {"unsigned char"})
            cursor = unary(postinc, "++", True, BYTE_PTR)
            require(register(cursor) == "next", "expected the old input pointer")
            typed(bits, UINT)
            require(register(bits) == "bits", "wrong byte shift count")
            advance = stmts[index + 1]
            require(advance.get("opcode") == "+=" and register(advance["inner"][0]) == "bits",
                    "expected the bit-count update immediately after the load")
            typed(advance["inner"][0], UINT)
            literal = expression(advance["inner"][1])
            typed(literal, UINT)
            if literal.get("castKind") == "IntegralCast":
                literal, = literal["inner"]
            require(literal["kind"] == "IntegerLiteral", "expected a fixed increase in the bit count")
            width = int(literal["value"])
            require(0 <= width < 2**32, "bit-count increment outside unsigned int")
            widths.append(width)
            if mutation is None:
                pos = literal["range"]["begin"]
                mutation = pos.get("spellingLoc", pos)["offset"]
    require(len(widths) == count, f"expected {count} input-byte sequences, found {len(widths)}")
    return widths, mutation


def match_copy(body, locals_by_id, registers):
    """Import the forward copy and its loop latch, including which value each ++/-- uses."""
    loops = []
    for loop in walk(body):
        if loop.get("kind") != "DoStmt":
            continue
        block, test = loop["inner"]
        statements = block.get("inner", [])
        if block["kind"] != "CompoundStmt" or len(statements) != 1 or statements[0].get("opcode") != "=":
            continue
        dest, source = map(expression, statements[0]["inner"])
        if dest.get("opcode") != "*" or source.get("opcode") != "*":
            continue
        fields = []
        for deref in (dest, source):
            typed(deref, {"unsigned char"})
            step = expression(deref["inner"][0])
            require(step.get("opcode") == "++" and step["isPostfix"], "expected the old match pointer")
            typed(step, BYTE_PTR)
            field = decoder_register(step["inner"][0], locals_by_id, registers)
            require(field in {"put", "from", "from_", "next"}, "unknown match pointer")
            fields.append("from_" if field == "from" else field)
        require(fields[0] != fields[1], "match copy increments the same pointer twice")
        test = expression(test)
        require(test.get("opcode") == "--" and not test["isPostfix"], "expected a decremented match count")
        typed(test, UINT)
        count = expression(test["inner"][0])
        counter = decoder_register(count, locals_by_id, registers)
        require(counter in {"copy", "left", "bits"}, "unknown match count")
        pos = location(count["range"]["end"])
        loops.append(([*fields, counter], (pos["offset"], pos["tokLen"])))
    require(len(loops) == 1, f"expected one forward match-copy loop, found {len(loops)}")
    return loops[0]


def code_length_order(body, state):
    """Read the bound table and the postfix decoder-state subscript at both uses."""
    table, = [n for n in walk(body) if n.get("kind") == "VarDecl" and n["name"] == "order"]
    require(table.get("storageClass") == "static", "expected a static code-length permutation")
    typed(table, {"const unsigned short[19]"})
    init, = table["inner"]
    require(init["kind"] == "InitListExpr" and len(init["inner"]) == 19, "expected 19 code lengths")
    values = []
    for element in init["inner"]:
        literal = expression(element)
        typed(literal, {"unsigned short"})
        if literal.get("castKind") == "IntegralCast":
            literal, = literal["inner"]
        require(literal["kind"] == "IntegerLiteral", "expected an integer code-length index")
        value = int(literal["value"])
        require(0 <= value < 2**16, "initializer exceeds unsigned short")
        values.append(value)
    first = init["inner"][0]["range"]["begin"]
    first = first.get("spellingLoc", first)

    uses = []
    postfix_span = None
    for subscript in walk(body):
        if subscript.get("kind") != "ArraySubscriptExpr":
            continue
        array, index = subscript["inner"]
        if array.get("castKind") != "ArrayToPointerDecay":
            continue
        binding = expression(array["inner"][0]).get("referencedDecl", {}).get("id")
        if binding != table["id"]:
            continue
        typed(subscript, {"const unsigned short"})
        index = expression(index)
        require(index.get("opcode") == "++" and index["isPostfix"], "expected the old permutation index")
        member = expression(index["inner"][0])
        require(member.get("kind") == "MemberExpr" and member["isArrow"] and
                variable(expression(member["inner"][0]))["id"] == state["id"],
                "permutation index must belong to the current decoder state")
        typed(index, UINT)
        typed(member, UINT)
        require(member["name"].isascii() and member["name"].isidentifier(), "invalid permutation index field")
        uses.append(member["name"])
        if postfix_span is None:
            start, end = (location(index["range"][k]) for k in ("begin", "end"))
            postfix_span = (start["offset"], end["offset"] + end["tokLen"])
    require(len(uses) == 2 and sum(n.get("referencedDecl", {}).get("id") == table["id"] for n in walk(body)) == 2,
            "expected exactly two reads of the code-length permutation")
    return values, uses, (first["offset"], first["tokLen"]), postfix_span


def mode_block(body, state, large):
    """Locate the main decoder switch and verify the origin of its selector."""
    def wanted_switch(node):
        if node.get("kind") != "SwitchStmt":
            return False
        cases = sum(item.get("kind") == "CaseStmt" for item in node["inner"][1]["inner"])
        return cases >= 30 if large else cases == len(BACK_MODES)
    switch, = [n for n in walk(body) if wanted_switch(n)]
    selector, block = switch["inner"]
    if selector.get("castKind") == "IntegralCast":
        selector, = selector["inner"]
    mode = expression(selector)
    if mode.get("kind") == "DeclRefExpr":
        # The emitter can save the mode in a fresh scalar immediately before the switch.
        typed(mode, UINT)
        ident = variable(mode)["id"]
        siblings, = [n["inner"] for n in walk(body) if n.get("kind") == "CompoundStmt"
                     and any(x.get("id") == switch["id"] for x in n.get("inner", []))]
        index = next(i for i, x in enumerate(siblings) if x["id"] == switch["id"])
        require(index > 0 and siblings[index - 1].get("opcode") == "=", "missing switch selector assignment")
        lhs, rhs = siblings[index - 1]["inner"]
        require(variable(expression(lhs))["id"] == ident, "unrelated mode temporary")
        if rhs.get("castKind") == "IntegralCast":
            rhs, = rhs["inner"]
        mode = expression(rhs)
    require(mode.get("kind") == "MemberExpr" and mode["isArrow"] and mode["name"] == "mode"
            and variable(expression(mode["inner"][0]))["id"] == state["id"], "wrong decoder mode selector")

    return block


def back_cases(body, state, registers):
    """Recover all inflateBack arms, preserving statement order."""
    block = mode_block(body, state, False)
    arms = {}
    key = None
    for stmt in block["inner"]:
        kind = stmt["kind"]
        if kind in {"CaseStmt", "DefaultStmt"}:
            key = "default"
            if kind == "CaseStmt":
                literal = stmt["inner"][0]
                if literal.get("castKind") == "IntegralCast":
                    literal, = literal["inner"]
                require(literal["kind"] == "ConstantExpr", "expected a constant mode")
                value, = literal["inner"]
                if registers is None:
                    decl = variable(value)
                    require(decl["kind"] == "EnumConstantDecl" and decl["name"] in BACK_MODES, "unknown source mode")
                    key = BACK_MODES[decl["name"]]
                else:
                    require(value["kind"] == "IntegerLiteral", "expected an emitted mode value")
                    key = int(value["value"])
            require(key not in arms, "duplicate mode")
            arms[key] = [stmt["inner"][-1]]
        else:
            require(key is not None, "unexpected statement before the first decoder mode")
            arms[key].append(stmt)
    require(set(arms) == set(BACK_MODES.values()) | {"default"}, "wrong decoder mode partition")
    return arms


class TableCall(NamedTuple):
    kind: int
    lens: str
    offset: str | None
    count: str | int
    next_field: str
    width: str
    work: str
    width_span: tuple


def back_tables(arm, state, locals_by_id, registers):
    """Read the three table-builder calls from the TABLE arm in execution order."""
    calls = []
    types = ("codetype", "unsigned short *", "unsigned int", "code **", "unsigned int *", "unsigned short *")

    def member(node, allowed):
        node = expression(node)
        require(node.get("kind") == "MemberExpr" and node["isArrow"] and node["name"] in allowed
                and variable(expression(node["inner"][0]))["id"] == state["id"], "wrong decoder table field")
        return node["name"]

    def array(node):
        node = expression(node)
        require(node.get("castKind") == "ArrayToPointerDecay", "expected embedded decoder array")
        return member(node["inner"][0], {"lens", "work"})

    def addressed(node, allowed):
        node = expression(node)
        require(node.get("kind") == "UnaryOperator" and node["opcode"] == "&", "expected table output address")
        field = expression(node["inner"][0])
        end = location(field["range"]["end"])
        return member(field, allowed), (end["offset"], end["tokLen"])

    for stmt in arm:
        for assignment in walk(stmt):
            if assignment.get("kind") != "BinaryOperator" or assignment.get("opcode") != "=":
                continue
            lhs, rhs = assignment["inner"]
            call = expression(rhs)
            if call.get("kind") != "CallExpr":
                continue
            fn, *args = call["inner"]
            if fn.get("castKind") != "FunctionToPointerDecay" or variable(fn["inner"][0])["name"] != "inflate_table":
                continue
            require(decoder_register(lhs, locals_by_id, registers) == "ret", "missing table-builder return value")
            require(tuple(a["type"]["qualType"] for a in args) == types, "wrong inflate_table call signature")
            selector, lens, count, dst, bits, work = args
            if selector.get("castKind") == "IntegralCast":
                selector, = selector["inner"]
            selector = expression(selector)
            if selector["kind"] == "IntegerLiteral":
                kind = int(selector["value"])
            else:
                enum = variable(selector)
                require(enum["kind"] == "EnumConstantDecl", "expected table kind")
                kind = {"CODES": 0, "LENS": 1, "DISTS": 2}[enum["name"]]
            lens = expression(lens)
            offset = None
            if lens.get("kind") == "BinaryOperator" and lens["opcode"] == "+":
                lens, index = lens["inner"]
                offset = member(index, {"nlen", "ndist"})
            count = expression(count)
            if count.get("castKind") == "IntegralCast":
                count, = count["inner"]
            count = int(count["value"]) if count["kind"] == "IntegerLiteral" else member(count, {"nlen", "ndist"})
            next_field, _ = addressed(dst, {"next"})
            width, span = addressed(bits, {"lenbits", "distbits"})
            calls.append(TableCall(kind, array(lens), offset, count, next_field, width, array(work), span))
    require(len(calls) == 3, "expected three Huffman builders in the dynamic-block arm")
    return calls


def back_exits(body, arms, locals_by_id, registers):
    """Read the signed return assignment and jump at each of the three terminal modes."""
    label, = [n for n in walk(body) if n.get("kind") == "LabelStmt" and n["name"] == "inf_leave"]
    exits = []
    for key in (BACK_MODES["DONE"], BACK_MODES["BAD"], "default"):
        assignment, jump = arms[key]
        require(assignment.get("opcode") == "=" and jump["kind"] == "GotoStmt"
                and jump.get("targetLabelDeclId") == label["declId"], "expected return assignment and exit jump")
        lhs, rhs = assignment["inner"]
        lhs = expression(lhs)
        typed(lhs, {"int"})
        if registers is not None and lhs.get("kind") == "MemberExpr" and lhs["isArrow"]:
            base = expression(lhs["inner"][0])
            require(lhs["name"] == "ret" and base.get("opcode") == "&"
                    and variable(expression(base["inner"][0]))["id"] == registers["id"], "wrong return register")
        else:
            require(decoder_register(lhs, locals_by_id, registers) == "ret", "wrong return register")
        first, last = (location(rhs["range"][end]) for end in ("begin", "end"))
        number = expression(rhs)
        negative = number.get("opcode") == "-"
        if negative:
            number, = number["inner"]
        require(number["kind"] == "IntegerLiteral", "expected a signed return code")
        typed(number, {"int"})
        value = int(number["value"])
        exits.append((-value if negative else value, first["offset"], last["offset"] + last["tokLen"]))
    return exits


class FastCall(NamedTuple):
    guards: list
    size: str
    loads: list
    mutations: list


def back_fast(arm, stream, state, locals_by_id, registers):
    """Import the LEN fast guard, called function, arguments and six reloads."""
    branch = arm[0]
    if registers is not None:
        label, end = arm
        require(label["kind"] == "LabelStmt" and end["kind"] == "BreakStmt", "expected generated LEN case")
        block, = label["inner"]
        branch, = block["inner"]
    require(branch["kind"] == "IfStmt" and len(branch["inner"]) == (3 if registers else 2),
            "expected leading LEN threshold test")
    test, yes, *_ = branch["inner"]
    test = expression(test)
    require(test.get("opcode") == "&&", "expected both fast margins")
    guards = []
    mutations = []

    def mutate(node, replacement):
        loc = node["range"]["end"]
        pos = loc.get("spellingLoc", loc)
        mutations.append((pos["offset"], pos["tokLen"], replacement))

    for part in test["inner"]:
        part = expression(part)
        require(part.get("opcode") == ">=", "expected unsigned minimum for fast decoder")
        reg, number = part["inner"]
        typed(reg, UINT)
        typed(number, UINT)
        if number.get("castKind") == "IntegralCast":
            number, = number["inner"]
        require(number["kind"] == "IntegerLiteral", "expected literal fast margin")
        name = decoder_register(reg, locals_by_id, registers)
        require(name in ("have", "have_", "left"), "expected fast input/output counter")
        guards.append(("have_" if name == "have" else name, int(number["value"])))
        mutate(number, str(int(number["value"]) + 1).encode())

    statements = yes["inner"]
    if registers is None:
        restore, call, reload, end = statements
        require(end["kind"] == "BreakStmt", "fast case must leave the mode switch")
        for macro in (restore, reload):
            require(macro["kind"] == "DoStmt" and macro["inner"][1].get("value") == "0"
                    and len(macro["inner"][0]["inner"]) == 6, "expected six unconditional register assignments")
        loads = reload["inner"][0]["inner"]
    else:
        require(len(statements) == 13, "expected writeback, fast call and reload")
        call = statements[6]
        loads = statements[7:]
    require(call["kind"] == "CallExpr", "missing fast decoder call")
    fn, arg, count = call["inner"]
    require(fn.get("castKind") == "FunctionToPointerDecay" and variable(fn["inner"][0])["name"] == "inflate_fast"
            and variable(arg)["id"] == stream["id"], "wrong fast decoder or stream")
    count = expression(count)
    typed(count, UINT)
    require(count["kind"] == "MemberExpr" and count["isArrow"] and count["name"] in {"wsize", "whave"}
            and variable(expression(count["inner"][0]))["id"] == state["id"], "wrong fast decoder state")
    mutate(count, b"whave")
    readbacks = []
    for stmt in loads:
        require(stmt.get("opcode") == "=", "expected direct reload")
        lhs, rhs = stmt["inner"]
        name = decoder_register(lhs, locals_by_id, registers)
        name = "have_" if name == "have" else name
        require(name in REGISTERS, "expected a decoder register destination")
        typed(lhs, REGISTERS[name])
        field = expression(rhs)
        require(field["kind"] == "MemberExpr" and field["isArrow"] and field["name"] in MEMBERS,
                "expected reload from a stream or state field")
        state_field = field["name"] in {"bits", "hold"}
        require(variable(expression(field["inner"][0]))["id"] == (state if state_field else stream)["id"],
                "wrong fast reload record")
        typed(field, REGISTERS[name])
        readbacks.append((name, "s" if state_field else "z", field["name"]))
        if name == "next":
            mutate(field, b"next_out")
    require([x[0] for x in readbacks] == ["put", "left", "next", "have_", "hold", "bits"],
            "unexpected reload destination order")
    return FastCall(guards, count["name"], readbacks, mutations)


def output_waits(body, state, locals_by_id, registers):
    """Read the first branch of MATCH and LIT and resolve its exit label."""
    modes = {"MATCH": 16204, "LIT": 16205}
    block = mode_block(body, state, True)
    leave, = [n for n in walk(body) if n.get("kind") == "LabelStmt" and n["name"] == "inf_leave"]
    guards = {}
    for case in block["inner"]:
        if case["kind"] != "CaseStmt":
            continue
        literal, stmt = case["inner"]
        if literal.get("castKind") == "IntegralCast":
            literal, = literal["inner"]
        require(literal["kind"] == "ConstantExpr", "expected constant decode mode")
        value, = literal["inner"]
        if registers is None:
            mode = variable(value)["name"]
        else:
            require(value["kind"] == "IntegerLiteral", "expected numeric decode mode")
            mode = next((name for name, n in modes.items() if n == int(value["value"])), None)
        if mode not in modes:
            continue
        if registers is not None:
            require(stmt["kind"] == "LabelStmt", "missing generated mode entry")
            stmt, = stmt["inner"]
            require(stmt["kind"] == "CompoundStmt", "expected generated mode body")
            stmt = stmt["inner"][0]
        require(stmt["kind"] == "IfStmt" and len(stmt["inner"]) == 2, "expected immediate output-room guard")
        test, jump = stmt["inner"]
        if jump["kind"] == "CompoundStmt":
            jump, = jump["inner"]
        require(jump["kind"] == "GotoStmt" and jump["targetLabelDeclId"] == leave["declId"],
                "output-room test must jump to inf_leave")
        test = expression(test)
        require(test.get("opcode") == "==", "expected equality test for output room")
        arg, literal = test["inner"]
        typed(arg, UINT)
        if literal.get("castKind") == "IntegralCast":
            literal, = literal["inner"]
        require(literal["kind"] == "IntegerLiteral", "expected literal output-room threshold")
        field = decoder_register(arg, locals_by_id, registers)
        require(field in ("left", "have", "have_"), "unexpected counter in output-room guard")
        span = location(expression(arg)["range"]["end"])
        require(mode not in guards, "duplicate output mode")
        guards[mode] = ("have_" if field == "have" else field, int(literal["value"]), span["offset"], span["tokLen"])
    require(guards.keys() == modes.keys(), "missing output-room guards")
    return guards


class DecoderSites(NamedTuple):
    restores: list
    counter_mutation: tuple
    guards: list
    cursor_mutations: list
    appends: tuple
    input_bytes: tuple
    order_table: tuple
    match_loop: tuple
    exits: list
    repeat: tuple
    stored: tuple | None
    tables: list
    output_guards: dict
    fast: FastCall | None
    finish: tuple | None


def extract(data, folder, inputs, reference, function, signature, site_count):
    if reference and function == "inflateBack":
        data += b"\n" + b"\n".join(f'_Static_assert({name} == {value}, "unexpected mode");'.encode()
                                  for name, value in BACK_MODES.items())
        data += b'\n_Static_assert(CODES == 0 && LENS == 1 && DISTS == 2, "unexpected table kinds");'
    if reference and function == "inflate":
        data += b'\n_Static_assert(MATCH == 16204 && LIT == 16205, "unexpected output modes");'
    nodes = clang(data, inputs.flags, folder, compiler=inputs.compiler, name=function)
    fn, = [n for n in nodes if n.get("name") == function and function_body(n)]
    loc = location(fn["loc"])
    require("includedFrom" not in loc and data[loc["offset"]:][:loc["tokLen"]] == function.encode()
            and fn["type"]["qualType"] == signature, f"expected the public {function} body")
    stream = next(n for n in fn["inner"] if n.get("kind") == "ParmVarDecl")
    typed(stream, {"z_stream *"})
    body = function_body(fn)
    state_name = "state" if reference else "st"
    state, = [n for n in walk(body) if n.get("kind") == "VarDecl" and n["name"] == state_name]
    typed(state, {"struct inflate_state *"})
    registers = None
    locals_by_id = {}
    if reference:
        locals_by_id = {n["id"]: n["name"] for line in body["inner"] if line["kind"] == "DeclStmt"
                        for n in line["inner"] if n.get("kind") == "VarDecl"}
    else:
        registers, = [n for n in walk(body) if n.get("kind") == "VarDecl" and n["name"] == "registers"]
        typed(registers, {"Zlib_Inflate_IL"})
    direct_cursor = None
    if not reference and function == "inflateBack":
        candidate, = [n for n in walk(body) if n.get("kind") == "VarDecl" and n["name"] == "cell"]
        if candidate.get("init") == "c" and expression(candidate["inner"][0]).get("kind") == "MemberExpr":
            direct_cursor = candidate
            locals_by_id[candidate["id"]] = "next"
    sites = []
    mutation = None
    for block in walk(body):
        if block.get("kind") != "CompoundStmt":
            continue
        stmts = block.get("inner", [])
        for i, stmt in enumerate(stmts):
            if stmt.get("opcode") != "=" or stmt["inner"][0].get("name") != "next_out":
                continue
            if reference:
                expansion = block["range"]["begin"].get("expansionLoc", {})
                start = expansion.get("offset", -1)
                require(data[start:start + 7] == b"RESTORE" and i == 0 and len(stmts) == 6,
                        "expected the complete RESTORE macro body")
            else:
                first = read(stmt["inner"][1])
                require(first.get("kind") == "MemberExpr" and not first["isArrow"], "expected a decoder local")
                frame = variable(first["inner"][0])
                if frame["id"] != registers["id"]:
                    require(i > 0 and stmts[i - 1]["kind"] == "DeclStmt", "expected a fresh decoder snapshot")
                    snapshot, = stmts[i - 1]["inner"]
                    require(snapshot["id"] == frame["id"] and snapshot.get("init") == "c"
                            and variable(snapshot["inner"][0])["id"] == registers["id"],
                            "snapshot must copy the current decoder locals")
                typed(frame, {"Zlib_Inflate_IL"})
            writes = []
            for assignment in stmts[i:i + 6]:
                require(assignment.get("kind") == "BinaryOperator" and assignment.get("opcode") == "=",
                        "expected six consecutive field assignments")
                lhs, rhs = assignment["inner"]
                require(lhs.get("kind") == "MemberExpr" and lhs["isArrow"], "expected a direct field store")
                field = lhs["name"]
                require(field in MEMBERS, f"unexpected field {field}")
                typed(lhs, MEMBERS[field])
                root = variable(expression(lhs["inner"][0]))
                target = "st" if field in ("hold", "bits") else "p"
                require(root["id"] == (state if target == "st" else stream)["id"], "wrong destination pointer")
                value = read(rhs)
                if reference:
                    name = locals_by_id.get(variable(value)["id"])
                    name = "have_" if name == "have" else name
                elif direct_cursor and value.get("kind") == "DeclRefExpr" and variable(value)["id"] == direct_cursor["id"]:
                    name = "next"
                else:
                    require(value.get("kind") == "MemberExpr" and not value["isArrow"]
                            and variable(value["inner"][0])["id"] == frame["id"], "wrong decoder frame")
                    name = value["name"]
                require(name in REGISTERS and REGISTERS[name] == MEMBERS[field], "invalid register type")
                typed(value, REGISTERS[name])
                writes.append((target, field, name))
                if field == "avail_out" and name == "left" and mutation is None:
                    end = value["range"]["end"]
                    offset = end.get("spellingLoc", end)["offset"]
                    require(data[offset:offset + 4] == b"left", "expected the actual register token")
                    mutation = (offset, b"have" if reference else b"have_")
            require(len(writes) == 6, "truncated restore block")
            sites.append(writes)
    require(len(sites) == site_count, f"{function}: expected {site_count} restore sites, found {len(sites)}")
    guards = []
    if function == "inflateBack":
        bits = None
        if reference:
            bits, = [n for n in walk(body) if n.get("kind") == "VarDecl" and n["name"] == "bits"]
        guards = bit_tests(body, state, bits, None if reference else registers)
    cursor_mutations = callback_cursor_sites(fn, reference, direct_cursor) if function == "inflateBack" else []
    appends = length_appends(body, state, reference)
    indices = [field for field, _ in appends.values()]
    mutation_index = next((offset for field, offset in appends.values() if field == "have"), None)
    arms = back_cases(body, state, registers) if function == "inflateBack" else {}
    term = back_terms(fn, state, locals_by_id, registers) if arms else None
    return DecoderSites(sites, mutation, guards, cursor_mutations, (indices, mutation_index),
                        input_bytes(body, locals_by_id, registers, 14 if function == "inflateBack" else 23),
                        code_length_order(body, state), match_copy(body, locals_by_id, registers),
                        back_exits(body, arms, locals_by_id, registers) if arms else [],
                        repeated_length(body, appends, locals_by_id, registers),
                        back_stored_case(fn, term, arms[BACK_MODES["STORED"]]) if arms else None,
                        back_tables(arms[BACK_MODES["TABLE"]], state, locals_by_id, registers) if arms else [],
                        output_waits(body, state, locals_by_id, registers) if function == "inflate" else {},
                        back_fast(arms[BACK_MODES["LEN"]], stream, state, locals_by_id, registers) if arms else None,
                        back_finish(fn, term) if arms else None)


def table_call_checks(tables):
    result = []
    for index, args in enumerate(tables):
        action = ("tabBWith build c", "tabLensWith build c", "tabLensTail1With build c 0")[index]
        result.append("open Zlib.Infback Zlib.Infback.Safety Zlib.Inftrees in")
        result.append(f"example (build : TableBuilder) (c : DecoderCtx) : {action} = (do")
        if index == 2:
            result.append("  wrS c.st fun s => {s with distcode := s.next, distbits := 8}")
        else:
            width = 7 if index == 0 else 10
            result.append("  wrS c.st fun s => {s with next := codesP c.st, lencode := codesP c.st, lenbits := " + str(width) + "}")
        result.append("  let s ← ldInflateState c.st")
        lens = f"({args.lens}P c.st)"
        if args.offset:
            lens = f"(← {lens}.add (s.{args.offset}.toNat : Int))"
        count = str(args.count) if isinstance(args.count, int) else f"s.{args.count}"
        result.append(f"  let (rc, nx, bits) ← build {args.kind} {lens} {count} s.{args.next_field} s.{args.width} ({args.work}P c.st)")
        result.append(f"  wrS c.st fun s => {{s with {args.next_field} := nx, {args.width} := bits}}")
        result.append("  modify fun l => {l with ret := rc}")
        tail = ("tabBTail", "tabLensTail1", "tabLensTail2")[index]
        result.append(f"  {tail} c rc) := Eq.refl _")
    return result


def check(work, sites, guards=(), indices=(), widths=(), order_table=None, match_fields=None, *, exits=(), repeat=None, stored=None, header=None, tables=(), output_guards=None, fast=None, reject=False):
    lines = ['import ZlibF.Proof.«inflate.c.main.macros»', 'open C Zlib.Inflate Zlib.Inflate.Proofs']
    if fast:
        lines.insert(0, 'import ZlibF.Proof.«infback.c.safety-fast»')
        guard = " && ".join(f"l.{name} >= {n}" for name, n in fast.guards)
        fields = ", ".join(f"{name} := {record}.{field}" for name, record, field in fast.loads)
        lines.extend(["open Zlib.Infback Zlib.Infback.Safety Zlib.Inffast in",
                      "example (c : DecoderCtx) : back_LEN c = (do", "  let l ← get",
                      f"  if {guard} then", "    RESTORE c.strm c.st",
                      f"    inflate_fast c.strm (← rdS c.st (·.{fast.size}))", "    LOAD c.strm c.st",
                      "    return", "  symLook c false lenIsLink (lenSym c)) := back_LEN_eq' c",
                      "open Zlib.Infback Zlib.Infback.Safety in",
                      "example (c : DecoderCtx) (r : ZStreamRef) (i : Nat) (h : Heap) (l : IL)",
                      "    (z : ZStream) (s : InflateState) (p : c.strm = some r) (q : c.st = some (.tab i))",
                      "    (hz : r.get h = some z) (hs : h.istates i = some s) :",
                      "    runX (LOAD c.strm c.st) l h = .ok ((.ok (), { l with " + fields + " }), h) :=",
                      "  LOAD_back_run p q hz hs l"])
    if output_guards:
        lines.insert(0, 'import ZlibF.Proof.«inflate.c.match-step»')
        for mode, (field, n, _, _) in output_guards.items():
            proof = "inflate_MATCH_wait c h l" if mode == "MATCH" else "inflate_LIT_full c l h"
            lines.extend([f"example (c : Ctx) (h : Heap) (l : IL) (stop : l.{field} = {n}) :",
                          f"    runX (inflate_{mode} c) l h = .ok ((.error Ex.leave, l), h) := by",
                          f"  apply {proof}", "  exact stop"])
    if tables:
        lines.insert(0, 'import ZlibF.Proof.«infback.c.safety-table-head»')
        lines.extend(table_call_checks(tables))
    if stored is not None:
        dst, src = stored
        lines.insert(0, 'import ZlibF.Proof.«infback.c.addressed-stored»')
        lines.extend(["example (st : InflateStatePtr) : Zlib.Infback.copyStoredInput st = (do",
                      "  let l ← get",
                      "  let k := if l.copy > l.have_ then l.have_ else l.copy",
                      "  let n := if k > l.left then l.left else k",
                      f"  memcpyB l.{dst} l.{src} n.toNat",
                      "  let nx ← l.next.add (n.toNat : Int)", "  let pt ← l.put.add (n.toNat : Int)",
                      "  set {l with copy := n, have_ := l.have_ - n, next := nx, left := l.left - n, put := pt}",
                      "  wrS st fun s => {s with length := s.length - n}) :=",
                      "  Zlib.Infback.AddressedStored.copy_source st"])
    if header is not None:
        width, mask, shift, complement, bad, length_mask, next_mode, increment = header
        lines.insert(0, 'import ZlibF.Proof.«infback.c.addressed-stored»')
        lines.append(f"example : absorbInputByte = sourceInputByte {increment} := by with_reducible exact absorbInputByte_eq_source")
        lines.extend(["open Zlib.Infback Zlib.Infback.AddressedStored in",
                      "example (c : DecoderCtx) : back_STORED c = (do",
                      "  BYTEBITS", f"  Zlib.Infback.NEEDBITS c {width}",
                      "  let l ← get", f"  if (l.hold &&& ({mask} : UInt64)) != ((l.hold >>> {shift}) ^^^ ({complement} : UInt64)) then",
                      f'    liftM ((do setMsg c.strm "invalid stored block lengths"; setMode c.st {bad}) : M Unit)',
                      "    return", f"  wrS c.st fun s => {{s with length := l.hold.toUInt32 &&& {length_mask}}}",
                      "  INITBITS", "  xwhile (moreStored c.st) (storedTrip c)",
                      f"  setMode c.st {next_mode}) := back_STORED_loop c"])
    if exits:
        done, bad, other = (value for value, _, _ in exits)
        lines.insert(0, 'import ZlibF.Proof.«infback.c.back»')
        lines.extend(["open Zlib.Infback Zlib.Infback.Proofs in",
                      "example (c : DecoderCtx) (l : IL) (h : Heap) (m : UInt32)",
                      "    (read : rdS c.st (·.mode) h = .ok (m, h))",
                      f"    (a : m ≠ {BACK_MODES['TYPE']}) (b : m ≠ {BACK_MODES['STORED']})",
                      f"    (d : m ≠ {BACK_MODES['TABLE']}) (e : m ≠ {BACK_MODES['LEN']}) :",
                      "    runX (back_dispatch c) l h = .ok ((.error Ex.leave, { l with ret :=",
                      f"      if m = {BACK_MODES['DONE']} then ({done}) else if m = {BACK_MODES['BAD']} then ({bad})",
                      f"      else ({other}) }}), h) := back_dispatch_exit c l h m read a b d e"])
    if guards:
        lines.insert(0, 'import ZlibF.Proof.«infback.c.safety-inv»')
        for field, _ in guards:
            require(field.isascii() and field.isidentifier(), "invalid C member name")
            lines += ["example (c : Zlib.Infback.DecoderCtx) : Zlib.Infback.needExtra c =",
                      f"  xwhile (do return (← get).bits < (← rdS c.st (·.«{field}»))) (Zlib.Infback.PULLBYTE c) := rfl"]
    for writes in sites:
        lines.append("example (p : ZStreamPtr) (st : InflateStatePtr) (l : IL) (h : Heap) :")
        lines.append("    runX (RESTORE p st) l h = runX (monadLift (m := M) (do")
        for target, field, value in writes:
            update = "wrS" if target == "st" else "wrZ"
            lines.append(f"      {update} {target} fun x => {{ x with {field} := l.{value} }}")
        lines.append("      ) : X Unit) l h := RESTORE_stores p st l h")
    for field in indices:
        lines.append("example (st : InflateStatePtr) (value : UInt16) : (appendLength st value : M Unit) = (do")
        lines.append(f"  let index ← rdS st (·.«{field}»)")
        lines.append(f"  wrS st fun s => {{ s with «{field}» := s.«{field}» + 1 }}")
        lines.append("  Ptr.store (← (lensP st).add (index.toNat : Int)) value) := Eq.refl (appendLength st value)")
    for width in sorted(set(widths)):
        lines.append(f"example : absorbInputByte = sourceInputByte {width} := by with_reducible exact absorbInputByte_eq_source")
    if repeat is not None:
        counter, postfix, index, value = repeat
        tested = f"l.{counter}" if postfix else "n"
        lines.extend(["example (st : InflateStatePtr) : repeatCodeLength st =",
                      "  xwhile (do", "    let l ← get",
                      f"    let n := l.{counter} - 1", f"    set {{ l with {counter} := n }}",
                      f"    return {tested} != 0) (do", "    let l ← get",
                      f"    let old ← rdS st (·.«{index}»)",
                      f"    wrS st fun s => {{ s with «{index}» := s.«{index}» + 1 }}",
                      f"    Ptr.store (← (lensP st).add (old.toNat : Int)) l.{value}.toUInt16) :=",
                      "  by with_reducible exact Eq.refl (repeatCodeLength st)"])
    if match_fields is not None:
        dest, source, count = match_fields
        lines.extend(["example : copyMatchBytes = xdoWhile (do", "    let l ← get",
                      f"    let b ← load8 l.{source}", f"    store8 l.{dest} b",
                      f"    let dst ← l.{dest}.add 1", f"    let src ← l.{source}.add 1",
                      f"    set {{ l with {dest} := dst, {source} := src }}) (do", "    let l ← get",
                      f"    let n := l.{count} - 1", f"    set {{ l with {count} := n }}",
                      "    return n != 0) := Eq.refl copyMatchBytes"])
    if order_table is not None:
        values, uses, _, _ = order_table
        lines.insert(0, 'import ZlibF.Proof.«inflate.c.main.table2»')
        entries = ", ".join(str(x) for x in values)
        lines.append(f"example : order = (#[{entries}] : Array UInt16) := Eq.refl order")
        for field in sorted(set(uses)):
            lines.append("example (st : InflateStatePtr) (k : UInt16 → X Unit) : withLengthOrder st k = (do")
            lines.append("  let s ← ldInflateState st")
            lines.append(f"  wrS st fun v => {{ v with «{field}» := v.«{field}» + 1 }}")
            lines.append(f"  let index ← orderAt s.«{field}»")
            lines.append("  k index) := Eq.refl (withLengthOrder st k)")
        lines.append("example (h : Heap) (i : UInt32) (bound : i.toNat < 19) :")
        lines.append(f"    orderAt i h = .ok ((#[{entries}] : Array UInt16)[i.toNat]!, h) := orderAt_run h i bound")
        lines.append("example (h : Heap) (i : UInt32) (outside : 19 ≤ i.toNat) :")
        lines.append('    orderAt i h = .error (.ub "order index outside its array") := orderAt_outside h i outside')
    path = work / "CheckRestore.lean"
    path.write_text("\n".join(lines) + "\n")
    result = subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", path], cwd=ROOT,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if reject:
        require(result.returncode != 0 and "Type mismatch" in result.stdout,
                f"expected Lean to reject the changed C operation\n{result.stdout}")
    else:
        require(result.returncode == 0, result.stdout)


def main():
    module = "ZlibF.Proof.«infback.c.adapted-call»"
    subprocess.run(["lake", "build", "--wfail", module], cwd=ROOT, check=True)
    subprocess.run(["lake", "env", "leanchecker", "--fresh", module], cwd=ROOT, check=True)
    with tempfile.TemporaryDirectory(prefix="zlib-source-restore-") as directory:
        work = Path(directory)
        inputs = prepare_inputs(work, pinned=True)
        decoders = [
            ("inflate.c", "inflate", "int (z_streamp, int)", 3),
            ("infback.c", "inflateBack", "int (z_streamp, in_func, void *, out_func, void *)", 1),
        ]
        for filename, function, signature, count in decoders:
            reference_sites = None
            for name in ("reference", "lean"):
                folder = work / name
                data = (folder / filename).read_bytes()
                def parse(source):
                    return extract(source, folder, inputs, name == "reference", function, signature, count)

                result = parse(data)
                sites, mutation = result.restores, result.counter_mutation
                guards, cursor_mutations = result.guards, result.cursor_mutations
                indices, index_mutation = result.appends
                widths, byte_mutation = result.input_bytes
                fields, (count_at, count_len) = result.match_loop
                repeat, (start, end), value_offset = result.repeat
                check(work, sites, guards, indices, widths, result.order_table, fields, exits=result.exits,
                      repeat=repeat, output_guards=result.output_guards, fast=result.fast)
                if result.finish:
                    pos, size = result.finish
                    require(data[pos:pos + size] == b"wsize", "wrong final output length token")
                    try:
                        parse(data[:pos] + b"whave" + data[pos + size:])
                    except ValueError as exc:
                        if str(exc) != "wrong final output invocation or status":
                            raise
                    else:
                        raise ValueError("accepted a different final output length")
                    print(f"{name}/{filename}: final callback length, status, input writeback and return checked")
                if result.fast:
                    for pos, size, replacement in result.fast.mutations:
                        changed = data[:pos] + replacement + data[pos + size:]
                        check(work, [], fast=parse(changed).fast, reject=True)
                    print(f"{name}/{filename}: fast guard, call and reload checked, four changes rejected")
                if result.output_guards:
                    for field, _, pos, size in result.output_guards.values():
                        require(field == "left" and data[pos:pos + size] == b"left", "unexpected output-room counter")
                        changed = data[:pos] + (b"have" if name == "reference" else b"have_") + data[pos + size:]
                        check(work, [], output_guards=parse(changed).output_guards, reject=True)
                    print(f"{name}/{filename}: MATCH and LIT leave on zero output room, both counter mutations rejected")
                if result.tables:
                    check(work, [], tables=result.tables)
                    for call in result.tables:
                        pos, length = call.width_span
                        require(data[pos:pos + length] == call.width.encode(), "wrong table width token")
                        other = b"distbits" if call.width == "lenbits" else b"lenbits"
                        changed = data[:pos] + other + data[pos + length:]
                        wrong = parse(changed).tables
                        check(work, [], tables=wrong, reject=True)
                    print(f"{name}/{filename}: all three table calls checked, swapped root-width outputs rejected")
                if result.stored:
                    operands, (pos, token_len), header, (shift, shift_len) = result.stored
                    check(work, [], stored=operands, header=header)
                    changed = data[:pos] + (b"put" if name == "reference" else b"registers.put") + data[pos + token_len:]
                    wrong = parse(changed).stored.copy
                    require(wrong != operands, "stored-copy mutation had no effect")
                    check(work, [], stored=wrong, reject=True)
                    changed = data[:shift] + b"15" + data[shift + shift_len:]
                    wrong_header = parse(changed).stored.header
                    require(wrong_header != header, "stored complement mutation had no effect")
                    check(work, [], header=wrong_header, reject=True)
                    print(f"{name}/{filename}: stored header, callbacks and copy checked, wrong shift and cursor rejected")
                operand = data[start:end]
                require(operand.endswith(b"--"), "missing postfix repeat test")
                prefix = data[:start] + b"--(" + operand[:-2] + b")" + data[end:]
                require(data[value_offset:value_offset + 3] == b"len", "missing repeated length")
                other = data[:value_offset] + b"copy" + data[value_offset + 3:]
                for changed in (prefix, other):
                    wrong, _, _ = parse(changed).repeat
                    check(work, [], repeat=wrong, reject=True)
                print(f"{name}/{filename}: repeat test and stored value checked, both mutations rejected")
                for value, first, end in result.exits:
                    changed = data[:first] + str(value + 1).encode() + data[end:]
                    wrong = parse(changed).exits
                    check(work, [], exits=wrong, reject=True)
                if result.exits:
                    print(f"{name}/{filename}: all three terminal modes checked, changed return codes rejected")
                require(data[count_at:count_at + count_len] == b"copy", "missing match counter")
                changed = data[:count_at] + b"left" + data[count_at + count_len:]
                wrong_fields, _ = parse(changed).match_loop
                require(wrong_fields != fields, "match count mutation had no effect")
                check(work, [], match_fields=wrong_fields, reject=True)
                print(f"{name}/{filename}: forward match copy checked, wrong loop counter rejected")
                if reference_sites is None:
                    reference_sites = sites
                else:
                    require(sites == reference_sites, f"{function}: restore field order differs from patched C")
                values, _, (offset, size), (start, end) = result.order_table
                operand = data[start:end]
                require(operand.endswith(b"++"), "missing postfix increment token")
                changed = data[:start] + b"++(" + operand[:-2] + b")" + data[end:]
                try:
                    parse(changed)
                except ValueError as exc:
                    if str(exc) != "expected the old permutation index":
                        raise
                else:
                    raise ValueError("accepted the advanced permutation index")
                require(data[offset:offset + size] == b"16", "missing first code-length permutation entry")
                changed = data[:offset] + b"17" + data[offset + size:]
                wrong_table = parse(changed).order_table
                require(wrong_table[0] != values, "mutation left the imported code-length permutation unchanged")
                check(work, [], order_table=wrong_table, reject=True)
                print(f"{name}/{filename}: both postfix permutation reads checked, prefix increment and changed table rejected")
                require(byte_mutation is not None and data[byte_mutation:byte_mutation + 1] == b"8",
                        "missing input-byte width literal")
                changed = data[:byte_mutation] + b"7" + data[byte_mutation + 1:]
                wrong, _ = parse(changed).input_bytes
                require(wrong != widths, "width mutation left the imported input-byte steps unchanged")
                check(work, [], widths=wrong, reject=True)
                print(f"{name}/{filename}: {len(widths)} input-byte sequences checked, wrong bit-count increment rejected")
                require(index_mutation is not None and data[index_mutation:index_mutation + 4] == b"have",
                        "missing original index token")
                changed = data[:index_mutation] + b"nlen" + data[index_mutation + 4:]
                wrong, _ = parse(changed).appends
                require(wrong != indices, "index mutation left the imported appends unchanged")
                check(work, [], indices=wrong, reject=True)
                print(f"{name}/{filename}: both postfix code-length indices checked, field substitution rejected")
                for offset, size, replacement in cursor_mutations:
                    changed = data[:offset] + replacement + data[offset + size:]
                    try:
                        parse(changed)
                    except ValueError as exc:
                        if str(exc) != "wrong callback cursor":
                            raise
                    else:
                        raise ValueError("accepted a different local as the input callback cursor")
                if cursor_mutations:
                    print(f"{name} inflateBack: 15 input sites, 4 output sites, {len(cursor_mutations)} wrong-cursor mutations rejected")
                require(mutation is not None, "missing output counter to mutate")
                offset, replacement = mutation
                changed = data[:offset] + replacement + data[offset + 4:]
                mutated = parse(changed).restores
                check(work, mutated, reject=True)
                print(f"{name}/{filename}: {len(sites)} RESTORE site(s) checked, input/output count mutation rejected")
                if guards:
                    field, offset = guards[0]
                    require(field == "extra" and data[offset:offset + 5] == b"extra", "expected the live extra-bit count")
                    changed = data[:offset] + b"wsize" + data[offset + 5:]
                    mutated = parse(changed).guards
                    check(work, [], mutated, reject=True)
                    print(f"{name}/{filename}: both live extra-bit loop guards checked, field substitution rejected")


if __name__ == "__main__":
    main()
