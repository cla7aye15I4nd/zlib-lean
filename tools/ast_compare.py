"""Compare Clang C ASTs, retaining types, implicit conversions, bindings, and child order."""
import argparse
from collections import defaultdict
from itertools import count
import json
import os
from pathlib import Path
import re
import subprocess
import sys


def clang(data, flags, cwd, *, name=None, listing=False, compiler=None):
    cc = compiler if compiler is not None else [os.environ.get("CLANG", "clang")]
    cmd = [*cc, *flags, "-x", "c", "-fsyntax-only",
           "-Werror=implicit-function-declaration", "-Xclang", "-ast-list" if listing else "-ast-dump=json"]
    if name:
        cmd += ["-Xclang", "-ast-dump-filter", "-Xclang", name]
    proc = subprocess.run(cmd + ["-"], input=data, cwd=cwd, capture_output=True)
    if proc.returncode:
        raise ValueError(proc.stderr.decode(errors="replace").strip())
    if listing:
        return proc.stdout.decode().splitlines()
    text = proc.stdout.decode()
    decoder = json.JSONDecoder()
    nodes = []
    i = 0
    while i < len(text):
        if text[i].isspace():
            i += 1
            continue
        node, i = decoder.raw_decode(text, i)
        nodes.append(node)
    return nodes


def location(loc):
    return loc.get("expansionLoc", loc)


def main_decls(root):
    for node in root.get("inner", []):
        loc = location(node.get("loc", {}))
        if "offset" in loc and "includedFrom" not in loc:
            yield node


def function_body(node):
    return next((x for x in node.get("inner", []) if x.get("kind") == "CompoundStmt"), None)


class IncompleteAST(ValueError):
    """A selected node has a known semantic operand missing from the dump."""


def objects(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from objects(child)
    elif isinstance(value, list):
        for child in value:
            yield from objects(child)


def function_scope(root, name):
    """Select the definition and declarations reachable in Clang's JSON dump."""
    roots = root["inner"]
    matches = [n for n in main_decls(root)
               if n.get("name") == name and n["kind"] == "FunctionDecl" and function_body(n)]
    if len(matches) != 1:
        raise ValueError(f"expected one main-file definition of {name}, found {len(matches)}")
    owners = {}
    names = defaultdict(set)
    redeclarations = defaultdict(set)

    def index(node, owner):
        if node.get("kind", "").endswith("Decl") and "id" in node:
            owners[node["id"]] = owner
        if "previousDecl" in node:
            redeclarations[node["previousDecl"]].add(owner)
        for child in node.get("inner", []):
            index(child, owner)

    for top in roots:
        owner = top["id"]
        index(top, owner)
        if "name" in top:
            names[top["name"]].add(owner)

    by_id = {top["id"]: top for top in roots}
    pending = [matches[0]["id"]]
    selected = set()
    while pending:
        owner = pending.pop()
        if owner in selected:
            continue
        selected.add(owner)
        deps = set()
        for part in objects(by_id[owner]):
            if "id" in part:
                deps.update(redeclarations.get(part["id"], ()))
            for key, val in part.items():
                if not isinstance(val, str):
                    continue
                if val in owners and (key != "id" or part.get("kind", "").endswith("Decl")):
                    deps.add(owners[val])
                elif key in {"qualType", "desugaredQualType"}:
                    # Tags in "struct S *" and typedefs in function signatures
                    # often have no declaration pointer in the JSON.
                    for word in re.findall(r"[A-Za-z_]\w*", val):
                        deps.update(names.get(word, ()))
        pending.extend(deps - selected)
    return selected


class Canonical:
    """Replace process-local declaration pointers with stable lexical identities."""
    def __init__(self, roots, selected=None):
        self.bindings = {}
        self.local_names = {}
        self.selected = selected
        self.anonymous = {}
        self.last_file = ""
        self.last_line = 0
        for i, root in enumerate(roots):
            self.index(root, (i,))
            # Builtin typedefs can refer to compiler-created tags whose
            # definitions Clang omits even from a complete translation unit.
            for top in root.get("inner", []):
                if top.get("kind") == "TypedefDecl" and top.get("isImplicit"):
                    for part in objects(top):
                        tag = part.get("decl", {})
                        if tag.get("kind") == "RecordDecl" and tag.get("name"):
                            self.bindings.setdefault(tag["id"], ["builtin", "RecordDecl", tag["name"]])

    def read_location(self, loc):
        if "expansionLoc" in loc:
            self.read_location(loc["spellingLoc"])
            return self.read_location(loc["expansionLoc"])
        if "offset" not in loc:
            return None
        self.last_file = loc.get("file", self.last_file)
        self.last_line = loc.get("line", self.last_line)
        return f"{self.last_file}:{self.last_line}:{loc.get('col', 0)}"

    def index(self, node, path, slots=None):
        # Clang compresses repeated file/line values in its JSON stream.
        loc = self.read_location(node.get("loc", {}))
        bounds = node.get("range", {})
        self.read_location(bounds.get("begin", {}))
        self.read_location(bounds.get("end", {}))
        if loc and node.get("kind") in {"RecordDecl", "EnumDecl"} and not node.get("name"):
            self.anonymous[loc] = ".".join(map(str, path))
        kind = node.get("kind")
        if kind == "ParenExpr" and len(node.get("inner", [])) == 1:
            self.index(node["inner"][0], path, slots)
            return
        if kind == "FunctionDecl":
            # Clang can store VLA bounds and typeof operands as text without
            # a DeclRefExpr. Preserve names there to avoid guessing a binding.
            dependent = any(re.search(r"\[(?!\s*(?:\d+)?\s*\])|\b(?:typeof|__typeof__)\b", spelling)
                            for part in objects(node) for field, spelling in part.items()
                            if field in {"qualType", "desugaredQualType"})
            slots = None if dependent else count()
        name = node.get("name")
        if slots is not None and kind in {"VarDecl", "ParmVarDecl"}:
            has_symbol = node.get("storageClass") == "extern" or any(
                attr.get("kind") == "AsmLabelAttr" for attr in node.get("inner", []))
            if not has_symbol:
                name = self.local_names[node["id"]] = f"#{next(slots)}"
        if kind == "LabelStmt":
            self.bindings[node["declId"]] = ["LabelDecl", node["name"], list(path)]
        if "id" in node:
            self.bindings[node["id"]] = [kind, name, list(path)]
        included = count()
        for i, child in enumerate(x for x in node.get("inner", []) if x.get("kind") != "FullComment"):
            if self.selected is not None and kind == "TranslationUnitDecl":
                suffix = (next(included),) if child.get("id") in self.selected else (-1, i)
            else:
                suffix = (i,)
            self.index(child, path + suffix, slots)

    def clean(self, node):
        if isinstance(node, list):
            return [self.clean(item) for item in node if not isinstance(item, dict) or item.get("kind") != "FullComment"]
        if not isinstance(node, dict):
            return node
        if node.get("kind") in {"OffsetOfExpr", "GCCAsmStmt", "MSAsmStmt", "MaxFieldAlignmentAttr"}:
            raise IncompleteAST(f"Clang JSON omits operands of {node['kind']}")
        if node.get("kind") == "ParenExpr" and len(node.get("inner", [])) == 1:
            return self.clean(node["inner"][0])
        local = self.local_names.get(node.get("id"))
        result = {"name": local} if local is not None else {}
        for key, value in node.items():
            if key in {"loc", "range", "isUsed", "isReferenced"}:
                continue
            if key == "id" or (local is not None and key == "name"):
                continue
            if local is not None and key == "mangledName" and value == node.get("name"):
                result[key] = local
                continue
            if key in {"qualType", "desugaredQualType"}:
                def anonymous_name(match):
                    origin = match.group(2)
                    anchor = self.anonymous.get(origin)
                    return match[0] if anchor is None else "(" + match[1] + " declaration " + anchor + ")"
                result[key] = re.sub(r"\(((?:unnamed|anonymous)[^()]*) at ([^()]+:\d+:\d+)\)",
                                     anonymous_name, value)
            elif key in {"referencedDecl", "decl", "ownedTagDecl", "foundReferencedDecl"} and isinstance(value, dict):
                result[key] = self.clean(value)
                if value["id"] not in self.bindings:
                    raise ValueError(f"unresolved AST binding {key}")
                result[key]["binding"] = self.bindings[value["id"]]
            elif isinstance(value, str) and re.fullmatch(r"0x[0-9a-fA-F]+", value) and (
                    key.endswith(("Id", "Decl")) or key in {"decl", "targetLabelDeclId"}):
                if value not in self.bindings:
                    raise ValueError(f"unresolved AST binding {key}; refusing to compare")
                result[key] = self.bindings[value]
            else:
                result[key] = self.clean(value)
        if result.get("inner") == []:
            result.pop("inner")
        return result


def first_diff(a, b, path="$"):
    if type(a) is not type(b):
        return [path, type(a).__name__, type(b).__name__]
    if isinstance(a, dict):
        for k in sorted(a.keys() | b.keys(), key=lambda x: (x != "kind", x)):
            if k not in a or k not in b:
                return [path + "." + k, "present" if k in a else "absent", "present" if k in b else "absent"]
            diff = first_diff(a[k], b[k], path + "." + k)
            if diff:
                return diff
    elif isinstance(a, list):
        for i, (left, right) in enumerate(zip(a, b)):
            diff = first_diff(left, right, f"{path}[{i}]")
            if diff:
                return diff
        if len(a) != len(b):
            return [path + ".length", len(a), len(b)]
    elif a != b:
        return [path, a, b]
    return None


def tree(data, flags, cwd, function=None):
    root, = clang(data, flags, cwd)
    if function is not None:
        selected = function_scope(root, function)
        canon = Canonical([root], selected)
        return [canon.clean(node) for node in root["inner"] if node["id"] in selected]
    canon = Canonical([root])
    return canon.clean(root)


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--function", help="compare one definition and its referenced declarations")
    p.add_argument("expected", type=Path)
    p.add_argument("generated", type=Path)
    p.add_argument("flags", nargs=argparse.REMAINDER)
    args = p.parse_args()
    flags = args.flags
    if flags[:1] == ["--"]:
        flags = flags[1:]
    try:
        a = tree(args.expected.read_bytes(), flags, args.expected.parent, args.function)
        b = tree(args.generated.read_bytes(), flags, args.generated.parent, args.function)
        diff = first_diff(a, b)
        print(json.dumps(diff) if diff else "Equal C ASTs")
        sys.exit(int(diff is not None))
    except (OSError, ValueError) as e:
        sys.exit(f"AST comparison failed: {e}")
