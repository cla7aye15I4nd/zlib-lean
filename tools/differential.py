"""Run the fixed-seed, patched zlib compatibility suite against the compiled Lean model."""
import argparse
from itertools import zip_longest
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from reference import BUILD, ROOT, make_reference


def check(names):
    BUILD.mkdir(exist_ok=True)
    tests = ROOT / "tests"
    subprocess.run(["lake", "--dir", tests, "build", "--wfail", *["difftest_" + n for n in names]], check=True)
    with tempfile.TemporaryDirectory(dir=BUILD) as tmp:
        work = Path(tmp)
        ref = work / "reference"
        make_reference(ref, configure=True)
        cc = os.environ.get("CC", "cc")
        subprocess.run(["./configure", "--static"], cwd=ref, check=True, stdout=subprocess.DEVNULL)
        subprocess.run(["make", "-s", "libz.a"], cwd=ref, check=True)
        total = 0
        for name in names:
            oracle = work / ("c_" + name)
            subprocess.run([cc, "-O2", "-I", ref, tests / "c" / (name + ".c"), ref / "libz.a", "-o", oracle], check=True)
            inp = work / "input"
            with inp.open("wb") as stream:
                subprocess.run([sys.executable, tests / "gen" / (name + ".py")], stdout=stream, check=True)
            outputs = [work / "c.out", work / "lean.out"]
            for exe, path in zip([oracle, tests / ".lake/build/bin" / ("difftest_" + name)], outputs):
                with inp.open("rb") as src, path.open("wb") as dst:
                    subprocess.run([exe], stdin=src, stdout=dst, cwd=work, check=True)
            count = 0
            with inp.open("rb") as rows, outputs[0].open("rb") as left, outputs[1].open("rb") as right:
                for count, (case, a, b) in enumerate(zip_longest(rows, left, right), 1):
                    if None in (case, a, b) or a != b or a.startswith((b"BADINPUT", b"FAULT")):
                        raise ValueError(f"{name}, input {count}: C={str(a)[:160]} Lean={str(b)[:160]}")
            if not count:
                raise ValueError(f"{name}: empty input corpus")
            total += count
            print(f"{name}: {count} matching cases", flush=True)
        print(f"{total} cases matched across {len(names)} drivers")


if __name__ == "__main__":
    names = (ROOT / "tests/list.txt").read_text().split()
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--only", choices=names)
    args = p.parse_args()
    check([args.only] if args.only else names)
