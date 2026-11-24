"""Compare a deterministic Linux libz.a with independent C ABI units emitted by Lean."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
from typing import NamedTuple

from reference import BUILD, LOCK, ROOT, make_reference


def output(command, **kwargs):
    return subprocess.check_output(command, text=True, **kwargs).strip()


def sha(data):
    return hashlib.sha256(data).hexdigest()


class BuildInputs(NamedTuple):
    compiler: list[str]
    archiver: list[str]
    version: str
    target: str
    env: dict
    flags: list[str]


def prepare_inputs(work, *, pinned=False):
    """Produce the two configured source trees and the exact archive compiler flags."""
    cc = shlex.split(os.environ.get("CC", "clang"))
    ar = shlex.split(os.environ.get("AR", "llvm-ar"))
    version = output([*cc, "--version"]).splitlines()[0]
    toolchain = LOCK["clangAudit"]
    if pinned:
        if version != toolchain["version"]:
            raise ValueError(f"expected {toolchain['version']}, found {version}")
        cc.append("--target=" + toolchain["target"])
    target = output([*cc, "-dumpmachine"])
    if pinned and target != toolchain["target"]:
        raise ValueError(f"expected {toolchain['target']}, found {target}")
    if not target.startswith("x86_64-") or not target.endswith("linux-gnu"):
        raise ValueError(f"CC must target x86-64 Linux GNU, got {target}")

    # Emit into an empty directory, before materializing any reference files.
    lean = work / "lean"
    subprocess.run([ROOT / "bin/lean2c", "abi-sources", lean], cwd=ROOT, check=True)
    reference = work / "reference"
    make_reference(reference, configure=True)
    env = dict(os.environ, CC=shlex.join(cc), AR=shlex.join(ar), ARFLAGS="rcsD",
               RANLIB=os.environ.get("RANLIB", "llvm-ranlib"), CHOST=target,
               SOURCE_DATE_EPOCH="0", CFLAGS=f"-O3 -std={toolchain['standard']} -g0 -DNDEBUG -ffunction-sections")
    subprocess.run(["./configure", "--static"], cwd=reference, env=env, check=True)
    flags = shlex.split(output(["make", "-s", "-f", "Makefile", "-f", "-", "abi-flags"],
                               input="abi-flags:\n\t@echo $(CFLAGS)\n", cwd=reference, env=env))
    return BuildInputs(cc, ar, version, target, env, flags)


def compare(work, *, pinned=False):
    cc, ar, version, target, env, flags = prepare_inputs(work, pinned=pinned)
    lean = work / "lean"
    reference = work / "reference"
    subprocess.run(["make", "libz.a"], cwd=reference, env=env, check=True)
    expected = output([*ar, "t", reference / "libz.a"]).splitlines()
    if not expected or len(expected) != len(set(expected)):
        raise ValueError("unexpected reference archive layout")
    for source in sorted(lean.glob("*.c")):
        subprocess.run([*cc, *flags, "-c", source.name, "-o", source.stem + ".o"],
                       cwd=lean, env=env, check=True)
    available = {p.name for p in lean.glob("*.o")}
    unexpected = sorted(available - set(expected))
    present = [n for n in expected if n in available]
    missing = [n for n in expected if n not in available]
    name = "libz.partial.a" if missing or unexpected else "libz.a"
    archive = lean / name
    subprocess.run([*ar, "rcsD", name, *present, *unexpected], cwd=lean, env=env, check=True)
    reference_bytes = (reference / "libz.a").read_bytes()
    candidate_bytes = archive.read_bytes()
    objects = {}
    for member in present:
        original = (reference / member).read_bytes()
        generated = (lean / member).read_bytes()
        objects[member] = {"equal": original == generated, "reference_sha256": sha(original),
                           "lean_sha256": sha(generated)}
    equal = (not missing and not unexpected and all(obj["equal"] for obj in objects.values())
             and candidate_bytes == reference_bytes)
    report = {"pinned": pinned, "zlib": LOCK["zlib"], "patches": LOCK["patches"],
              "target": target, "compiler": version,
              "cflags": flags, "archiver": output([*ar, "--version"]).splitlines()[0],
              "reference": "reference/libz.a", "reference_sha256": sha(reference_bytes),
              "lean": "lean/" + name, "lean_sha256": sha(candidate_bytes), "objects": objects,
              "missing": missing, "unexpected": unexpected, "archive_equal": equal}
    (work / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    count = sum(item["equal"] for item in objects.values())
    print(f"{count}/{len(expected)} objects byte-identical; archive equal: {equal}")
    print(work / "report.json")
    return equal


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pinned", action="store_true", help="enforce the compiler and target in pins.json")
    parser.add_argument("--output", type=Path, help="new directory for this build")
    args = parser.parse_args()
    if args.output:
        work = args.output.resolve()
        work.mkdir(parents=True, exist_ok=False)
    else:
        BUILD.mkdir(exist_ok=True)
        work = Path(tempfile.mkdtemp(prefix="archive-", dir=BUILD))
    raise SystemExit(0 if compare(work, pinned=args.pinned) else 1)
