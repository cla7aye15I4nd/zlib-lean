import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from ast_compare import first_diff, tree


class ClangAST(unittest.TestCase):
    def compare(self, a, b):
        return first_diff(tree(a.encode(), [], ROOT), tree(b.encode(), [], ROOT))

    def test_macro_comments_layout(self):
        a = "#define ADD(x) ((x) + 1)\n/** input */ int f(int x) { return ADD(x); }"
        b = "int f(int x) {\n /* output */ return x + 1;\n}"
        self.assertIsNone(self.compare(a, b))

    def test_changed_macro(self):
        a = "#define OP <\nint f(int a, int b){ return a OP b; }"
        self.assertIsNotNone(self.compare(a, a.replace("OP <", "OP <=")))

    def test_binding_signedness_and_order(self):
        self.assertIsNone(self.compare("int f(int x){int y=x; {int x=y; return x;}}",
                                       "int f(int a){int b=a; {int c=b; return c;}}"))
        for a, b in [
            ("int f(int a,int b){return a;}", "int f(int a,int b){return b;}"),
            ("int f(int a){return a >> 1;}", "int f(unsigned a){return a >> 1;}"),
            ("int f(int a){a++;return a;}", "int f(int a){return a++;}"),
            ("int f(int a,int b){int v[a];return sizeof v;}",
             "int f(int b,int a){int v[a];return sizeof v;}"),
            ("extern int x; int f(void){int x=2; {int x=3; return x;}}",
             "extern int x; int f(void){int x=2; {int y=3; return x;}}"),
        ]:
            self.assertIsNotNone(self.compare(a, b))

    def test_anonymous_type_positions(self):
        src = "struct { int x; } a; struct { long x; } b; int f(void){return a.x;}"
        self.assertIsNone(self.compare(src, "/* layout */\n\n" + src))
        self.assertIsNotNone(self.compare(src, src.replace("return a.x", "return b.x")))

    def test_label_bindings(self):
        a = "int f(int x){if(x) goto yes; goto no; yes: return 1; no: return 0;}"
        self.assertIsNone(self.compare(a, a))
        self.assertIsNotNone(self.compare(a, a.replace("if(x) goto yes", "if(x) goto no")))

    def test_included_code(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            h = root / "helper.h"
            src = b'#include "helper.h"\nint f(void){return helper();}'
            h.write_text("static int helper(void){return 1;}")
            a = tree(src, [], root)
            h.write_text("static int helper(void){return 2;}")
            self.assertIsNotNone(first_diff(a, tree(src, [], root)))

    def test_function_header_dependencies(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            h = root / "helper.h"
            src = b'#include "helper.h"\nint f(const struct S *p){return helper(p);}'
            header = ("struct S { int x, y; }; typedef struct S Pair; "
                      "static int helper(const Pair *p){return p->x;}")
            h.write_text(header)
            a = tree(src, [], root, "f")
            h.write_text("typedef long Unused;\n" + header)
            self.assertIsNone(first_diff(a, tree(src, [], root, "f")))
            for changed in [header.replace("x, y", "y, x"), header.replace("p->x", "p->y")]:
                h.write_text(changed)
                self.assertIsNotNone(first_diff(a, tree(src, [], root, "f")))


class Baseline(unittest.TestCase):
    def test_sources(self):
        report = json.loads((ROOT / "build/ast-report.json").read_text())
        self.assertEqual(len(report["units"]), 15)
        self.assertFalse(report["missing_public"])
        self.assertFalse(report["missing_native_public"])
        self.assertEqual(report["macros"]["crc32.c"]["W"], {"lean": 4, "c": 4})
        self.assertEqual(sum(b["public"] for b in report["functions"].values()), 86)
        for path in ("adler32.c/adler32", "compress.c/compress", "crc32.c/crc32"):
            self.assertEqual(report["functions"][path]["status"], "equal")
        if report["pinned"]:
            self.assertEqual(report["functions"]["crc32.c/byte_swap"]["status"], "equal")
        self.assertEqual(report["functions"]["compress.c/compressBound"]["status"], "different")
        for path in ("crc32.h", "inffixed.h", "trees.h"):
            self.assertTrue(report["headers"][path]["byte_equal"])

    def test_byte_cli(self):
        exe = ROOT / ".lake/build/bin/lean2c"
        with tempfile.TemporaryDirectory() as tmp:
            a, b = [Path(tmp) / n for n in ("a", "b")]
            for p in (a, b):
                (p / "sub").mkdir(parents=True)
                (p / "sub/f.h").write_bytes(b"// comment\r\n")
            def compare():
                return subprocess.run([exe, "compare", a, b], capture_output=True, text=True)
            self.assertEqual(compare().returncode, 0)
            (b / "sub/f.h").write_bytes(b"// comment\n")
            result = compare()
            self.assertEqual(result.returncode, 1)
            self.assertIn("byte 10", result.stdout)
            (b / "sub/f.h").unlink()
            (b / "extra").touch()
            result = compare()
            self.assertEqual(result.returncode, 1)
            self.assertIn("missing", result.stdout)
            self.assertIn("extra", result.stdout)
