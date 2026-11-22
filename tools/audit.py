"""Audit the selected zlib build against independently emitted Lean C."""
import argparse
from collections import Counter
import json
import os
from pathlib import Path
import platform
import re
import shlex
import subprocess
import sys
import tempfile

from ast_compare import Canonical, clang, first_diff, function_body, main_decls, tree
from reference import BUILD, ROOT, make_reference

API = json.loads((ROOT / "tests/public-api.json").read_text())
PUBLIC = {e["function"]: e["implementation"] for e in API["apis"]
          if e["function"] not in API["undocumented"]["functions"]}
NAMESPACES = {"adler32": "Adler32", "compress": "Compress", "crc32": "Crc32", "deflate": "Deflate",
              "gzclose": "Gzclose", "gzlib": "Gzlib", "gzread": "Gzread", "gzwrite": "Gzwrite",
              "infback": "Infback", "inffast": "Inffast", "inflate": "Inflate", "inftrees": "Inftrees",
              "trees": "Trees", "uncompr": "Uncompr", "zutil": "Zutil"}


def configure(ref):
    env = {**os.environ, "CC": os.environ.get("CLANG", "clang")}
    subprocess.run(["./configure", "--static"], cwd=ref, env=env, check=True, stdout=subprocess.DEVNULL)
    result = subprocess.check_output(["make", "-s", "-f", "Makefile", "-f", "-", "audit-flags"],
                                    input=b"audit-flags:\n\t@echo $(CFLAGS) $(ZINC)\n", cwd=ref)
    return shlex.split(result.decode())


def functions(root):
    return {node["name"]: node for node in main_decls(root)
            if node["kind"] == "FunctionDecl" and function_body(node) is not None}


def candidate(data, body, emitted):
    bounds = body["range"]
    lo, hi = bounds["begin"], bounds["end"]
    if "offset" not in lo or "offset" not in hi:
        raise ValueError("function body boundaries originate from a macro")
    end = hi["offset"] + hi["tokLen"]
    if data[lo["offset"]:lo["offset"] + 1] != b"{" or data[end-1:end] != b"}":
        raise ValueError("invalid Clang function body range")
    return data[:lo["offset"]] + emitted.encode() + data[end:]


def native_types(directory, symbols, flags, cwd):
    # Parse the exact signatures of real backend definitions. A prototype from
    # another unit alone cannot establish that the model emitted a definition.
    wanted = set(symbols.values())
    prototypes = []
    signature = re.compile(r"^(?:LEAN_EXPORT|static) [^(){};]*?\b(\w+)\([^(){};]*\)\s*\{\s*$")
    for path in sorted(directory.rglob("*.c")):
        for line in path.read_text().splitlines():
            match = signature.match(line)
            if match and match[1] in wanted:
                prototypes.append(line[:line.rfind("{")] + ";")
    unit = "#include <lean/lean.h>\n" + "\n".join(prototypes)
    root, = clang(unit.encode(), flags, cwd)
    return {n["name"]: n["type"]["qualType"] for n in main_decls(root) if n["kind"] == "FunctionDecl"}


def check_bodies(ref, file, data, flags, root, bodies, symbols, signatures):
    src = functions(root)
    canon = Canonical([root])
    results = {}
    for name, node in src.items():
        symbol = PUBLIC.get(name, f"Zlib.{NAMESPACES[Path(file).stem]}.{name}")
        entry = {"file": file, "lean": symbol, "public": name in PUBLIC, "status": "unsupported"}
        native = symbols.get(symbol)
        if native in signatures:
            original = node["type"]["qualType"]
            actual = signatures[native]
            witness = ["$.type.qualType", original, actual] if original != actual else ["$.name", name, native]
            entry["native_declaration"] = {"symbol": native, "first_difference": witness}
        if symbol in bodies:
            try:
                edited = candidate(data, function_body(node), bodies[symbol])
                alt, = clang(edited, flags, ref)
                target = functions(alt)[name]
                diff = first_diff(canon.clean(function_body(node)), Canonical([alt]).clean(function_body(target)))
                entry["status"] = "different" if diff else "equal"
                if diff:
                    entry["first_difference"] = diff
            except ValueError as exc:
                entry["reason"] = str(exc).splitlines()[0]
        results[f"{file}/{name}"] = entry
    return results


def macro_values(data, flags, ref, expected):
    # Clang evaluates the active macro expression, even if it expands first to
    # another macro name. The enum probe keeps the original compilation context.
    names = [key for key, _ in expected]
    probes = ", ".join("lean2c_macro_" + name + " = " + name for name in names)
    nodes = clang(data + ("\nenum { " + probes + " };\n").encode(), flags, ref, name="lean2c_macro_")
    values = {}
    for n in nodes:
        expr = n["inner"][0]
        while expr["kind"] == "ImplicitCastExpr":
            expr = expr["inner"][0]
        if expr["kind"] != "ConstantExpr":
            raise ValueError(f"Clang did not evaluate {n['name']}")
        values[n["name"]] = int(expr["value"])
    return {key: {"lean": int(value), "c": values["lean2c_macro_" + key]}
            for key, value in expected}


def audit():
    BUILD.mkdir(exist_ok=True)
    subprocess.run([ROOT / "bin/lean2c", "emit", BUILD / "generated"], check=True)
    subprocess.run([ROOT / "bin/lean2c", "bodies", BUILD / "bodies.json"], check=True)
    subprocess.run([ROOT / "bin/lean2c", "macros", BUILD / "macros.json"], check=True)
    macros = dict(json.loads((BUILD / "macros.json").read_text()))
    subprocess.run([ROOT / "bin/lean2c", "symbols", BUILD / "symbols.json"], check=True)
    symbols = dict(json.loads((BUILD / "symbols.json").read_text()))
    bodies = dict(json.loads((BUILD / "bodies.json").read_text()))
    lean_prefix = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
    report = {"host": platform.platform(), "clang": subprocess.check_output(
        [os.environ.get("CLANG", "clang"), "--version"], text=True).splitlines()[0],
              "units": {}, "functions": {}, "headers": {}, "macros": {}}
    with tempfile.TemporaryDirectory(dir=BUILD) as tmp:
        ref = Path(tmp)
        units = make_reference(ref, configure=True)
        flags = [*configure(ref), "-I", str(Path(lean_prefix) / "include")]
        report["flags"] = [f.replace(lean_prefix, "<lean-prefix>") for f in flags]
        if {Path(f).stem for f in units} != set(NAMESPACES):
            raise ValueError("translation unit inventory changed")
        signatures = native_types(BUILD / "generated", symbols, flags, ref)
        for file in units:
            data = (ref / file).read_bytes()
            if file in macros:
                report["macros"][file] = macro_values(data, flags, ref, macros[file])
            root, = clang(data, flags, ref)
            # A missing definition name is already a structural mismatch. For
            # matching inventories, compare full nodes including type and body.
            native = (BUILD / "generated" / file).read_bytes()
            native_names = set(clang(native, flags, ref, listing=True))
            missing = sorted(set(functions(root)) - native_names)
            if missing:
                diff = ["$.FunctionDecl", missing[0], "absent from native declarations"]
            else:
                other, = clang(native, flags, ref)
                diff = first_diff(Canonical([root]).clean(root), Canonical([other]).clean(other))
            report["units"][file] = {"status": "different" if diff else "equal", "first_difference": diff}
            report["functions"].update(check_bodies(ref, file, data, flags, root, bodies, symbols, signatures))
        contexts = {"crc32.h": "crc32.c", "inffixed.h": "inftrees.c", "trees.h": "trees.c"}
        for h in sorted(ref.glob("*.h")):
            generated = BUILD / "generated" / h.name
            if not generated.is_file():
                report["headers"][h.name] = {"status": "no-source-emitter"}
                continue
            original = h.read_bytes()
            same_bytes = original == generated.read_bytes()
            diff = None
            if not same_bytes:
                # Parse inside the real including unit. inffixed.h is included
                # at block scope, so it cannot be parsed as a standalone header.
                context = (ref / contexts[h.name]).read_bytes()
                before = tree(context, flags, ref)
                try:
                    h.write_bytes(generated.read_bytes())
                    diff = first_diff(before, tree(context, flags, ref))
                finally:
                    h.write_bytes(original)
            report["headers"][h.name] = {"status": "different" if diff else "equal",
                                           "byte_equal": same_bytes, "first_difference": diff}
    seen = {key.split("/")[1] for key, item in report["functions"].items() if item["public"]}
    report["missing_public"] = sorted(PUBLIC.keys() - seen)
    report["missing_native_public"] = sorted(key for key, e in report["functions"].items()
                                            if e["public"] and "native_declaration" not in e)
    (BUILD / "ast-report.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-equal", action="store_true", help="require full source AST coverage and equality")
    args = parser.parse_args()
    result = audit()
    counts = Counter(e["status"] for e in result["functions"].values())
    print("Source-format function bodies:", dict(counts))
    print("Native translation units:", dict(Counter(e["status"] for e in result["units"].values())))
    print("Header sources:", dict(Counter(h["status"] for h in result["headers"].values())))
    print("Expected public functions missing from Clang:", result["missing_public"])
    print("Report: build/ast-report.json")
    macro_diffs = [(file, key) for file, group in result["macros"].items() for key, values in group.items()
                   if values["c"] != values["lean"]]
    print("Different target macro values:", macro_diffs)
    print("Expected public functions missing from emitted C:", result["missing_native_public"])
    if result["missing_public"] or result["missing_native_public"] or macro_diffs:
        sys.exit(2)
    if args.require_equal:
        sys.exit(int(any(e["status"] != "equal" for e in result["units"].values())
                     or any(e["status"] != "equal" for e in result["functions"].values())
                     or any(h["status"] != "equal" for h in result["headers"].values())))
