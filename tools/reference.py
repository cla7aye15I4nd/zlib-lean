"""Materialize the independent C baseline from Git objects and the pinned patch series."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / "build"
LOCK = json.loads((ROOT / "pins.json").read_text())
UPSTREAM = ROOT / "upstream"


def git(*args):
    return subprocess.check_output(["git", "-C", UPSTREAM, *args])


def make_reference(dest, *, configure=False):
    pin = LOCK["zlib"]
    paths = [name for name in git("ls-tree", "--name-only", pin).decode().splitlines()
             if name.endswith((".c", ".h"))]
    if not paths:
        raise ValueError("no library sources found at the pinned zlib commit")
    if configure:
        paths += ["configure", "Makefile.in", "zconf.h.in", "zlib.pc.in", "zlib.map"]
    patches = sorted((ROOT / "patches").glob("*.patch"))
    digests = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in patches}
    if digests != LOCK["patches"]:
        raise ValueError("patch names or contents differ from pins.json")
    dest.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory() as tmp:
        stage = Path(tmp)
        subprocess.run(["git", "init", "-q", stage], check=True)
        for name in paths:
            (stage / name).write_bytes(git("show", f"{pin}:{name}"))
        subprocess.run(["git", "-C", stage, "apply", "--whitespace=nowarn", *patches], check=True)
        unexpected = set(os.listdir(dest)) - set(paths)
        if unexpected:
            raise ValueError(f"unexpected files in reference destination {dest}: {sorted(unexpected)}")
        for name in paths:
            shutil.copyfile(stage / name, dest / name)
    if configure:
        (dest / "configure").chmod(0o755)
    return sorted(n for n in paths if n.endswith(".c"))


if __name__ == "__main__":
    make_reference(BUILD / "reference")
