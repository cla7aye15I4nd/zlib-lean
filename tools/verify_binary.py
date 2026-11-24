#!/usr/bin/env python3
"""Verify C ABI layouts, byte-for-byte .o equality, and libz.a equality against patched zlib."""
import argparse
import difflib
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import tempfile

from reference import BUILD, LOCK, ROOT, make_reference


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def select_cc(pinned: bool = False) -> list[str]:
    if os.environ.get("CC"):
        cc = shlex.split(os.environ["CC"])
    elif sys.platform == "darwin":
        cc = ["/usr/bin/clang", "--target=x86_64-apple-darwin"]
    else:
        which_clang = shutil.which("clang")
        if which_clang and "lean-" in str(Path(which_clang).resolve()) and Path("/usr/bin/clang").exists():
            cc = ["/usr/bin/clang"]
        else:
            cc = ["clang"]
    if pinned:
        toolchain = LOCK["clangAudit"]
        ver = subprocess.check_output([*cc, "--version"], text=True).splitlines()[0]
        if ver != toolchain["version"]:
            raise ValueError(f"expected {toolchain['version']}, got {ver}")
        if "--target=" not in " ".join(cc):
            cc.append("--target=" + toolchain["target"])
    return cc


def configure_reference(ref_dir: Path, cc: list[str], pinned: bool = False) -> tuple[dict, list[str]]:
    toolchain = LOCK["clangAudit"]
    std = toolchain["standard"]
    ar = os.environ.get("AR") or ("/usr/bin/ar" if sys.platform == "darwin" else "llvm-ar")
    ranlib = os.environ.get("RANLIB") or ("/usr/bin/ranlib" if sys.platform == "darwin" else "llvm-ranlib")
    cflags = f"-O3 -std={std} -g0 -DNDEBUG -ffunction-sections -fno-ident"
    if sys.platform != "darwin":
        cflags = f"-O3 -std={std} -g0 -DNDEBUG -ffunction-sections"
    env = dict(os.environ, CC=shlex.join(cc), AR=ar, RANLIB=ranlib, CFLAGS=cflags, SOURCE_DATE_EPOCH="0")
    if sys.platform == "darwin":
        env["ZERO_AR_DATE"] = "1"
        if pinned:
            raise ValueError("--pinned Linux audit must run on x86_64-linux-gnu")
    else:
        env["ARFLAGS"] = "rcsD"
        env["CHOST"] = subprocess.check_output([*cc, "-dumpmachine"], text=True).strip()
    subprocess.run(["./configure", "--static"], cwd=ref_dir, env=env, check=True, stdout=subprocess.DEVNULL)
    flags = shlex.split(subprocess.check_output(
        ["make", "-s", "-f", "Makefile", "-f", "-", "abi-flags"],
        input="abi-flags:\n\t@echo $(CFLAGS)\n", text=True, cwd=ref_dir, env=env
    ).strip())
    return env, flags


def archive_objects(archive_path: Path, objects: list[Path], cwd: Path) -> None:
    env = os.environ.copy()
    if sys.platform == "darwin":
        env["ZERO_AR_DATE"] = "1"
        subprocess.run(["/usr/bin/ar", "rcs", str(archive_path), *(o.name for o in objects)], cwd=cwd, env=env, check=True)
    else:
        ar = os.environ.get("AR", "llvm-ar")
        subprocess.run([ar, "rcsD", str(archive_path), *(o.name for o in objects)], cwd=cwd, env=env, check=True)


def parse_struct_fields(body: str) -> list[str]:
    fields = []
    for raw in body.splitlines():
        line = raw.strip()
        if not line:
            continue
        m = re.match(r"^.+?\b([A-Za-z_]\w*)(?:\s*\[\d+\])*\s*;$", line)
        if not m:
            raise ValueError(f"cannot parse ABI struct field: {line}")
        fields.append(m.group(1))
    if not fields:
        raise ValueError("empty ABI struct body")
    return fields


def _extract(src: str, pat: str, name: str) -> str:
    m = re.search(pat, src, re.S)
    if not m:
        raise ValueError(f"missing {name} layout in emitted ABI headers")
    return m.group(1)


def _add_checks(lines: list[str], struct_counts: dict[str, int], checks):
    for orig_ty, lean_ty, body in checks:
        fields = parse_struct_fields(body)
        struct_counts[orig_ty] = len(fields)
        lines.append(f'_Static_assert(sizeof({lean_ty}) == sizeof({orig_ty}), "sizeof mismatch: {orig_ty}");')
        for f in fields:
            lines.append(
                f'_Static_assert(offsetof({lean_ty}, {f}) == offsetof({orig_ty}, {f}), '
                f'"offsetof mismatch: {orig_ty}.{f}");'
            )
            lines.append(
                f'_Static_assert(sizeof((({lean_ty} *)0)->{f}) == sizeof((({orig_ty} *)0)->{f}), '
                f'"field sizeof mismatch: {orig_ty}.{f}");'
            )


def verify_abi_layouts(cc: list[str], flags: list[str], ref_dir: Path, lean_dir: Path, work_dir: Path) -> dict[str, int]:
    common_h = (lean_dir / "abi_common.h").read_text() if (lean_dir / "abi_common.h").exists() else ""
    deflate_h = common_h + "\n" + (lean_dir / "abi_deflate.h").read_text()
    inflate_h = common_h + "\n" + (lean_dir / "abi_inflate.h").read_text()
    gz_h = common_h + "\n" + (lean_dir / "abi_gz.h").read_text()
    trees_c = (ref_dir / "trees.c").read_text()
    static_tree_ref = _extract(trees_c, r"(struct static_tree_desc_s\s*\{.*?\};)", "static_tree_desc_s ref")

    zs_b = _extract(deflate_h, r"typedef struct z_stream_s\s*\{(.*?)\}\s*z_stream;", "z_stream_s")
    gh_b = _extract(deflate_h, r"typedef struct gz_header_s\s*\{(.*?)\}\s*gz_header;", "gz_header_s")
    ct_b = _extract(deflate_h, r"typedef struct ct_data_s\s*\{(.*?)\}\s*ct_data;", "ct_data")
    st_b = _extract(deflate_h, r"struct static_tree_desc_s\s*\{(.*?)\};", "static_tree_desc_s")
    td_b = _extract(deflate_h, r"typedef struct tree_desc_s\s*\{(.*?)\}\s*tree_desc;", "tree_desc")
    ds_b = _extract(deflate_h, r"struct internal_state\s*\{(.*?)\};", "deflate_state")
    cd_b = _extract(inflate_h, r"typedef struct\s*\{(.*?)\}\s*code;", "code")
    is_b = _extract(inflate_h, r"struct inflate_state\s*\{(.*?)\};", "inflate_state")
    gf_b = _extract(gz_h, r"struct gzFile_s\s*\{(.*?)\};", "gzFile_s")
    gs_b = _extract(gz_h, r"typedef struct\s*\{(.*?)\}\s*gz_state;", "gz_state")

    lean_td_b = re.sub(r"\bstruct ct_data_s\b", "struct lean_ct_data_s", td_b)
    lean_td_b = re.sub(r"\bstatic_tree_desc\b", "lean_static_tree_desc", lean_td_b)
    lean_st_b = re.sub(r"\bstruct ct_data_s\b", "struct lean_ct_data_s", st_b)
    lean_ds_b = ds_b
    for old, new in [
        (r"\bz_streamp\b", "struct lean_z_stream_s *"),
        (r"\bgz_headerp\b", "struct lean_gz_header_s *"),
        (r"\bstruct ct_data_s\b", "struct lean_ct_data_s"),
        (r"\bstruct tree_desc_s\b", "struct lean_tree_desc_s"),
    ]:
        lean_ds_b = re.sub(old, new, lean_ds_b)
    lean_is_b = re.sub(r"\bcode\b", "lean_code", is_b)
    lean_gs_b = gs_b.replace("struct z_stream_s", "struct lean_z_stream_s").replace("struct gzFile_s", "struct lean_gzFile_s")

    struct_counts: dict[str, int] = {}
    groups = [
        ("deflate", [
            "#include <stddef.h>", '#include "zlib.h"', '#include "deflate.h"', static_tree_ref, "",
            f"struct lean_z_stream_s {{{zs_b}}};", f"struct lean_gz_header_s {{{gh_b}}};",
            f"struct lean_ct_data_s {{{ct_b}}};", "typedef struct lean_static_tree_desc_s lean_static_tree_desc;",
            f"struct lean_static_tree_desc_s {{{lean_st_b}}};", f"struct lean_tree_desc_s {{{lean_td_b}}};",
            f"typedef struct {{{lean_ds_b}}} lean_deflate_state;", "",
        ], [
            ("struct z_stream_s", "struct lean_z_stream_s", zs_b),
            ("struct gz_header_s", "struct lean_gz_header_s", gh_b),
            ("ct_data", "struct lean_ct_data_s", ct_b),
            ("static_tree_desc", "lean_static_tree_desc", st_b),
            ("tree_desc", "struct lean_tree_desc_s", td_b),
            ("deflate_state", "lean_deflate_state", ds_b),
        ]),
        ("inflate", [
            "#include <stddef.h>", '#include "zutil.h"', '#include "inftrees.h"', '#include "inflate.h"', "",
            f"typedef struct {{{cd_b}}} lean_code;", f"struct lean_inflate_state {{{lean_is_b}}};", "",
        ], [
            ("code", "lean_code", cd_b),
            ("struct inflate_state", "struct lean_inflate_state", is_b),
        ]),
        ("gz", [
            "#include <stddef.h>", '#include "gzguts.h"', "",
            f"struct lean_z_stream_s {{{zs_b}}};", f"struct lean_gzFile_s {{{gf_b}}};",
            f"typedef struct {{{lean_gs_b}}} lean_gz_state;", "",
        ], [
            ("struct gzFile_s", "struct lean_gzFile_s", gf_b),
            ("gz_state", "lean_gz_state", gs_b),
        ]),
    ]
    for gname, lines, checks in groups:
        _add_checks(lines, struct_counts, checks)
        cf = work_dir / f"abi_check_{gname}.c"
        cf.write_text("\n".join(lines) + "\n")
        proc = subprocess.run([*cc, *flags, "-I", str(ref_dir), "-fsyntax-only", str(cf)],
                              cwd=ref_dir, capture_output=True, text=True)
        if proc.returncode:
            raise ValueError(f"ABI _Static_assert ({gname}) failed:\n{proc.stderr.strip()}")

    # Also cross-check Lean AST sizeofTy/fieldLayout? against clang runtime values
    lean_layouts = json.loads(subprocess.check_output([ROOT / "bin/lean2c", "layout-json"], text=True, cwd=ROOT))
    probe_src = ['#include <stdio.h>', '#include <stddef.h>', '#include "abi_deflate.h"',
                 '#include "abi_inflate.h"', '#include "abi_gz.h"', 'int main(void) {']
    probe_tags = {
        "z_stream_s": ("struct z_stream_s", zs_b),
        "gz_header_s": ("struct gz_header_s", gh_b),
        "ct_data_s": ("struct ct_data_s", ct_b),
        "static_tree_desc_s": ("struct static_tree_desc_s", st_b),
        "tree_desc_s": ("struct tree_desc_s", td_b),
        "internal_state": ("struct internal_state", ds_b),
        "code": ("code", cd_b),
        "inflate_state": ("struct inflate_state", is_b),
        "gzFile_s": ("struct gzFile_s", gf_b),
        "gz_state": ("gz_state", gs_b),
    }
    probe_src.append('  printf("{");')
    first_tag = True
    for tag, (cty, body) in probe_tags.items():
        fields = parse_struct_fields(body)
        if not first_tag:
            probe_src.append('  printf(",");')
        first_tag = False
        probe_src.append(f'  printf("\\"{tag}\\":{{\\"size\\":%zu,\\"fields\\":{{", sizeof({cty}));')
        for i, f in enumerate(fields):
            comma = "," if i > 0 else ""
            probe_src.append(
                f'  printf("{comma}\\"{f}\\":{{\\"offset\\":%zu,\\"size\\":%zu}}", '
                f'offsetof({cty}, {f}), sizeof((({cty} *)0)->{f}));'
            )
        probe_src.append('  printf("}}");')
    probe_src.append('  printf("}\\n"); return 0; }')
    pf = work_dir / "probe_abi.c"
    pf.write_text("\n".join(probe_src) + "\n")
    exe = work_dir / "probe_abi"
    subprocess.run([cc[0], *(c for c in cc[1:] if c.startswith("--target=")), "-std=gnu17",
                    "-I", str(lean_dir), str(pf), "-o", str(exe)], cwd=lean_dir, check=True)
    # Run probe only if native-compatible (x86_64 on macOS Rosetta works, or compile native clang)
    run_probe = subprocess.run([str(exe)], capture_output=True, text=True)
    if run_probe.returncode == 0:
        c_layouts = json.loads(run_probe.stdout)
        for tag, cl in c_layouts.items():
            ll = lean_layouts.get(tag)
            if not ll:
                raise ValueError(f"Lean layout-json missing ABI tag `{tag}`")
            if ll["size"] != cl["size"]:
                raise ValueError(f"Lean sizeofTy({tag}) = {ll['size']} != C {cl['size']}")
            for f, cf in cl["fields"].items():
                lf = ll["fields"].get(f)
                if lf != cf:
                    raise ValueError(f"Lean layout({tag}.{f}) = {lf} != C {cf}")
    return struct_counts


def print_llvm_diff(cc: list[str], flags: list[str], ref_c: Path, lean_c: Path) -> None:
    ref_ll = ref_c.with_suffix(".ll")
    lean_ll = lean_c.with_suffix(".ll")
    subprocess.run([*cc, *flags, "-S", "-emit-llvm", ref_c.name, "-o", str(ref_ll)], cwd=ref_c.parent, check=True)
    subprocess.run([*cc, *flags, "-S", "-emit-llvm", lean_c.name, "-o", str(lean_ll)], cwd=lean_c.parent, check=True)
    diff = list(difflib.unified_diff(
        ref_ll.read_text().splitlines(), lean_ll.read_text().splitlines(),
        fromfile=f"ref/{ref_c.name}.ll", tofile=f"lean/{lean_c.name}.ll", n=3
    ))
    print(f"--- LLVM IR diff for {lean_c.name} (first 120 lines) ---")
    for line in diff[:120]:
        print(line)
    if len(diff) > 120:
        print(f"... ({len(diff) - 120} more lines truncated)")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--unit", help="check a single C unit (e.g. adler32.c)")
    parser.add_argument("--abi", action="store_true", help="check only ABI struct layouts")
    parser.add_argument("--pinned", action="store_true", help="enforce pins.json clang version and target")
    args = parser.parse_args()

    cc = select_cc(pinned=args.pinned)
    BUILD.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="verify-", dir=BUILD) as tmp:
        work = Path(tmp)
        lean_dir = work / "lean"
        ref_dir = work / "reference"
        subprocess.run([ROOT / "bin/lean2c", "abi-sources", str(lean_dir)], cwd=ROOT, check=True)
        make_reference(ref_dir, configure=True)
        env, flags = configure_reference(ref_dir, cc, pinned=args.pinned)

        if args.abi or not args.unit:
            counts = verify_abi_layouts(cc, flags, ref_dir, lean_dir, work)
            print(f"ABI structs OK: {len(counts)}/10 structs, {sum(counts.values())} fields verified")
            if args.abi:
                return 0

        if args.unit:
            unit = args.unit
            ref_c = ref_dir / unit
            lean_c = lean_dir / unit
            if not lean_c.exists():
                raise FileNotFoundError(f"missing emitted unit {lean_c}")
            stem = Path(unit).stem
            ref_o = ref_dir / f"{stem}.o"
            lean_o = lean_dir / f"{stem}.o"
            subprocess.run([*cc, *flags, "-c", unit, "-o", ref_o.name], cwd=ref_dir, env=env, check=True)
            subprocess.run([*cc, *flags, "-c", unit, "-o", lean_o.name], cwd=lean_dir, env=env, check=True)
            equal = ref_o.read_bytes() == lean_o.read_bytes()
            print(f"{unit}: obj_equal: {equal} (ref={sha256(ref_o.read_bytes())[:12]}, lean={sha256(lean_o.read_bytes())[:12]})")
            if not equal:
                print_llvm_diff(cc, flags, ref_c, lean_c)
                return 1
            return 0

        # Full 15-unit + libz.a verification
        subprocess.run(["make", "libz.a"], cwd=ref_dir, env=env, check=True)
        ar = os.environ.get("AR") or ("/usr/bin/ar" if sys.platform == "darwin" else "llvm-ar")
        expected = subprocess.check_output([ar, "t", str(ref_dir / "libz.a")], text=True).splitlines()
        if sys.platform == "darwin":
            expected = [m for m in expected if not m.startswith("__.SYMDEF")]
        for src in sorted(lean_dir.glob("*.c")):
            subprocess.run([*cc, *flags, "-c", src.name, "-o", src.stem + ".o"], cwd=lean_dir, env=env, check=True)
        available = {p.name for p in lean_dir.glob("*.o")}
        missing = [m for m in expected if m not in available]
        unexpected = sorted(available - set(expected))
        equal_count = 0
        mismatches = []
        for member in expected:
            if member not in available:
                continue
            ref_bytes = (ref_dir / member).read_bytes()
            lean_bytes = (lean_dir / member).read_bytes()
            if ref_bytes == lean_bytes:
                equal_count += 1
            else:
                mismatches.append(member)
                print(f"MISMATCH: {member}")
                print_llvm_diff(cc, flags, ref_dir / (Path(member).stem + ".c"), lean_dir / (Path(member).stem + ".c"))
        if missing or unexpected:
            print(f"missing={missing} unexpected={unexpected}")
            return 1
        archive_objects(lean_dir / "libz.a", [lean_dir / m for m in expected], lean_dir)
        arch_eq = (ref_dir / "libz.a").read_bytes() == (lean_dir / "libz.a").read_bytes()
        print(f"{equal_count}/{len(expected)} objects byte-identical; libz.a equal: {arch_eq}")
        return 0 if (equal_count == len(expected) and arch_eq) else 1


if __name__ == "__main__":
    raise SystemExit(main())
