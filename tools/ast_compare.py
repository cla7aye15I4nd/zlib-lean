"""Compare Clang C ASTs, retaining types, implicit conversions, bindings, and child order."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys


def clang(data, flags, cwd, *, name=None, listing=False):
    cmd = [os.environ.get("CLANG", "clang"), *flags, "-x", "c", "-fsyntax-only",
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


class Canonical:
    """Replace process-local declaration pointers with stable lexical identities."""
    def __init__(self, roots):
        self.bindings = {}
        self.anonymous = {}
        self.last_file = ""
        self.last_line = 0
        for i, root in enumerate(roots):
            self.index(root, (i,))

    def read_location(self, loc):
        if "expansionLoc" in loc:
            self.read_location(loc["spellingLoc"])
            return self.read_location(loc["expansionLoc"])
        if "offset" not in loc:
            return None
        self.last_file = loc.get("file", self.last_file)
        self.last_line = loc.get("line", self.last_line)
        return f"{self.last_file}:{self.last_line}:{loc.get('col', 0)}"

    def index(self, node, path):
        # Clang compresses repeated file/line values in its JSON stream.
        loc = self.read_location(node.get("loc", {}))
        bounds = node.get("range", {})
        self.read_location(bounds.get("begin", {}))
        self.read_location(bounds.get("end", {}))
        if loc and node.get("kind") in {"RecordDecl", "EnumDecl"} and not node.get("name"):
            self.anonymous[loc] = ".".join(map(str, path))
        if node.get("kind") == "ParenExpr" and len(node.get("inner", [])) == 1:
            self.index(node["inner"][0], path)
            return
        if node.get("kind") == "LabelStmt":
            self.bindings[node["declId"]] = ["LabelDecl", node["name"], list(path)]
        if "id" in node:
            self.bindings[node["id"]] = [node.get("kind"), node.get("name"), list(path)]
        for i, child in enumerate(x for x in node.get("inner", []) if x.get("kind") != "FullComment"):
            self.index(child, path + (i,))

    def clean(self, node):
        if isinstance(node, list):
            return [self.clean(item) for item in node if not isinstance(item, dict) or item.get("kind") != "FullComment"]
        if not isinstance(node, dict):
            return node
        if node.get("kind") == "ParenExpr" and len(node.get("inner", [])) == 1:
            return self.clean(node["inner"][0])
        result = {}
        for key, value in node.items():
            if key in {"loc", "range", "isUsed", "isReferenced"}:
                continue
            if key == "id":
                continue
            if key in {"qualType", "desugaredQualType"}:
                def anonymous_name(match):
                    origin = match.group(2)
                    anchor = self.anonymous.get(origin)
                    return match[0] if anchor is None else "(" + match[1] + " declaration " + anchor + ")"
                result[key] = re.sub(r"\(((?:unnamed|anonymous)[^()]*) at ([^()]+:\d+:\d+)\)",
                                     anonymous_name, value)
            elif key == "referencedDecl" and isinstance(value, dict):
                result[key] = self.clean(value)
                if value.get("id") in self.bindings:
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


def tree(data, flags, cwd):
    root, = clang(data, flags, cwd)
    canon = Canonical([root])
    return canon.clean(root)


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("expected", type=Path)
    p.add_argument("generated", type=Path)
    p.add_argument("flags", nargs=argparse.REMAINDER)
    args = p.parse_args()
    flags = args.flags
    if flags[:1] == ["--"]:
        flags = flags[1:]
    try:
        a = tree(args.expected.read_bytes(), flags, args.expected.parent)
        b = tree(args.generated.read_bytes(), flags, args.generated.parent)
        diff = first_diff(a, b)
        print(json.dumps(diff) if diff else "Equal C ASTs")
        sys.exit(int(diff is not None))
    except (OSError, ValueError) as e:
        sys.exit(f"AST comparison failed: {e}")
