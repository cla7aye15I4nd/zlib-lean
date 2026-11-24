"""Exercise inflate_table pointer arguments through the actual standalone emitter."""
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class TableFields(unittest.TestCase):
    def test_outputs_and_snapshots(self):
        subprocess.run(["lake", "build", "--wfail", "Lean2C.Simple", "ZlibF.Zlib.«inflate.c»"],
                       cwd=ROOT, check=True)
        search_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"],
                                              cwd=ROOT, text=True).strip()
        prefix = subprocess.check_output(["lake", "env", "lean", "--print-prefix"],
                                         cwd=ROOT, text=True).strip()
        lean = Path(prefix) / "bin/lean"
        with tempfile.TemporaryDirectory() as temp:
            work = Path(temp)
            env = dict(os.environ, LEAN_PATH=os.pathsep.join([temp, search_path]))
            (work / "TableFields.lean").write_bytes((ROOT / "tests/lean/TableFields.lean").read_bytes())
            (work / "Emit.lean").write_text('import TableFields\n'
                                            '#eval IO.FS.writeFile "table-fields-generated.c" tableFieldsSource%\n')
            subprocess.run([lean, "-DwarningAsError=true", "-o", "TableFields.olean", "TableFields.lean"],
                           cwd=work, env=env, check=True)
            subprocess.run([lean, "Emit.lean"], cwd=work, env=env, check=True)
            # Once inflate_table writes the actual fields, forward has only its return left.
            source = (work / "table-fields-generated.c").read_text()
            forward = source.split("int forward(", 1)[1].split("\n}", 1)[0]
            after_call = forward.split("inflate_table(", 1)[1].split(";", 1)[1]
            self.assertRegex(after_call, r"^\s*return \w+;\s*$")
            cc = shlex.split(os.environ.get("CC", "cc"))
            subprocess.run([*cc, "-std=gnu17", "-O2", "-UNDEBUG", "-I", temp, ROOT / "tests/c/table-fields.c",
                            "-o", work / "table-fields"], cwd=ROOT, check=True)
            subprocess.run([work / "table-fields"], cwd=work, check=True)
