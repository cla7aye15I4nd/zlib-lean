"""Verify byte-identical object files and libz.a from standalone Lean C units, ABI layout checks, and lowered functions."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile

from ast_compare import clang
from audit import NAMESPACES, PUBLIC, candidate, configure, functions
from reference import BUILD, LOCK, ROOT, make_reference


GENERATED_HEADERS = ("crc32.h", "inffixed.h", "trees.h")


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def select_clang():
    cc = os.environ.get("CLANG")
    if cc:
        return cc
    which_clang = shutil.which("clang")
    if which_clang and "lean-" in str(Path(which_clang).resolve()) and Path("/usr/bin/clang").exists():
        return "/usr/bin/clang"
    return "clang"


def archive_objects(archive_path, objects):
    env = os.environ.copy()
    if sys.platform == "darwin":
        env["ZERO_AR_DATE"] = "1"
        cmd = ["ar", "rcs", str(archive_path), *(str(o) for o in objects)]
    else:
        cmd = ["ar", "rcsD", str(archive_path), *(str(o) for o in objects)]
    subprocess.run(cmd, check=True, env=env)


def parse_struct_fields(body):
    fields = []
    for raw in body.splitlines():
        line = raw.strip()
        if not line:
            continue
        match = re.match(r"^.+?\b([A-Za-z_]\w*)(?:\s*\[\d+\])?\s*;$", line)
        if not match:
            raise ValueError(f"cannot parse ABI struct field: {line}")
        fields.append(match.group(1))
    if not fields:
        raise ValueError("empty ABI struct body")
    return fields


def _extract(src, pat, name):
    m = re.search(pat, src, re.S)
    if not m:
        raise ValueError(f"missing {name} layout in abi-sources")
    return m.group(1)


def _add_checks(lines, struct_counts, checks):
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


def _run_abi_group(cc, flags, ref_dir, work_dir, name, lines):
    check_file = work_dir / f"abi_check_{name}.c"
    check_file.write_text("\n".join(lines) + "\n")
    proc = subprocess.run([cc, *flags, "-I", str(ref_dir), "-fsyntax-only", str(check_file)], cwd=ref_dir, capture_output=True, text=True)
    if proc.returncode:
        raise ValueError(f"ABI layout _Static_assert ({name}) failed:\n{proc.stderr.strip()}")


def verify_abi_layouts(cc, flags, ref_dir, abi_dir, work_dir):
    deflate_h = (abi_dir / "abi_deflate.h").read_text()
    inflate_h = (abi_dir / "abi_inflate.h").read_text()
    gz_h = (abi_dir / "abi_gz.h").read_text()
    trees_c = (ref_dir / "trees.c").read_text()
    static_tree_ref = _extract(trees_c, r"(struct static_tree_desc_s\s*\{.*?\};)", "static_tree_desc_s ref")

    zs_b = _extract(deflate_h, r"struct z_stream_s\s*\{(.*?)\};", "z_stream_s")
    gh_b = _extract(deflate_h, r"struct gz_header_s\s*\{(.*?)\};", "gz_header_s")
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

    struct_counts = {}

    lines_a = [
        "#include <stddef.h>",
        '#include "zlib.h"',
        '#include "deflate.h"',
        static_tree_ref,
        "",
        f"struct lean_z_stream_s {{{zs_b}}};",
        f"struct lean_gz_header_s {{{gh_b}}};",
        f"struct lean_ct_data_s {{{ct_b}}};",
        "typedef struct lean_static_tree_desc_s lean_static_tree_desc;",
        f"struct lean_static_tree_desc_s {{{lean_st_b}}};",
        f"struct lean_tree_desc_s {{{lean_td_b}}};",
        f"typedef struct {{{lean_ds_b}}} lean_deflate_state;",
        "",
    ]
    _add_checks(lines_a, struct_counts, [
        ("struct z_stream_s", "struct lean_z_stream_s", zs_b),
        ("struct gz_header_s", "struct lean_gz_header_s", gh_b),
        ("ct_data", "struct lean_ct_data_s", ct_b),
        ("static_tree_desc", "lean_static_tree_desc", st_b),
        ("tree_desc", "struct lean_tree_desc_s", td_b),
        ("deflate_state", "lean_deflate_state", ds_b),
    ])
    _run_abi_group(cc, flags, ref_dir, work_dir, "deflate", lines_a)

    lines_b = [
        "#include <stddef.h>",
        '#include "zutil.h"',
        '#include "inftrees.h"',
        '#include "inflate.h"',
        "",
        f"typedef struct {{{cd_b}}} lean_code;",
        f"struct lean_inflate_state {{{lean_is_b}}};",
        "",
    ]
    _add_checks(lines_b, struct_counts, [
        ("code", "lean_code", cd_b),
        ("struct inflate_state", "struct lean_inflate_state", is_b),
    ])
    _run_abi_group(cc, flags, ref_dir, work_dir, "inflate", lines_b)

    lines_c = [
        "#include <stddef.h>",
        '#include "gzguts.h"',
        "",
        f"struct lean_z_stream_s {{{zs_b}}};",
        f"struct lean_gzFile_s {{{gf_b}}};",
        f"typedef struct {{{lean_gs_b}}} lean_gz_state;",
        "",
    ]
    _add_checks(lines_c, struct_counts, [
        ("struct gzFile_s", "struct lean_gzFile_s", gf_b),
        ("gz_state", "lean_gz_state", gs_b),
    ])
    _run_abi_group(cc, flags, ref_dir, work_dir, "gz", lines_c)

    return struct_counts


def splice_unit(unit_path, flags, work_dir, unit_name, bodies):
    data = unit_path.read_bytes()
    root, = clang(data, flags, work_dir)
    unit_funcs = sorted(functions(root))
    replaced = []
    skipped = {}
    unlowered = 0

    for name in unit_funcs:
        symbol = PUBLIC.get(name, f"Zlib.{NAMESPACES[Path(unit_name).stem]}.{name}")
        if symbol not in bodies:
            unlowered += 1
            continue
        # Re-parse the current buffer before each splice because earlier replacements shift byte offsets.
        cur_root, = clang(data, flags, work_dir)
        node = functions(cur_root)[name]
        try:
            data = candidate(data, node, *bodies[symbol])
            replaced.append(f"{unit_name}/{name}")
        except ValueError as exc:
            skipped[f"{unit_name}/{name}"] = str(exc).splitlines()[0]

    unit_path.write_bytes(data)
    return replaced, skipped, unlowered


def build_and_verify(pinned=False):
    cc = select_clang()
    version = subprocess.check_output([cc, "--version"], text=True).splitlines()[0]
    if pinned and version != LOCK["clangAudit"]["version"]:
        raise ValueError(f"expected {LOCK['clangAudit']['version']}, found {version}")

    os.environ["CLANG"] = cc
    os.environ["CC"] = cc

    BUILD.mkdir(exist_ok=True)
    subprocess.run([ROOT / "bin/lean2c", "emit", BUILD / "generated"], check=True)
    subprocess.run([ROOT / "bin/lean2c", "candidates", BUILD / "candidates.json"], check=True)
    bodies = dict(json.loads((BUILD / "candidates.json").read_text()))

    headers_replaced = {}
    standalone_units = []
    spliced_units = []
    functions_replaced = []
    functions_skipped = {}
    unlowered_count = 0
    unit_reports = {}

    with tempfile.TemporaryDirectory(dir=BUILD) as tmp:
        work = Path(tmp)
        ref_dir = work / "ref"
        lean_dir = work / "lean"
        abi_dir = work / "abi"

        subprocess.run([ROOT / "bin/lean2c", "abi-sources", abi_dir], check=True)
        units = make_reference(ref_dir, configure=True)
        make_reference(lean_dir, configure=True)

        flags = configure(ref_dir, pinned)
        lean_flags = configure(lean_dir, pinned)
        if flags != lean_flags:
            raise ValueError(f"configure flags diverged: ref={flags} lean={lean_flags}")

        target = subprocess.check_output([cc, *flags, "-print-target-triple"], text=True).strip()
        if pinned and target != LOCK["clangAudit"]["target"]:
            raise ValueError(f"configured compiler has unexpected target {target}")

        abi_layout_checks = verify_abi_layouts(cc, flags, ref_dir, abi_dir, work)

        for header in GENERATED_HEADERS:
            gen_bytes = (BUILD / "generated" / header).read_bytes()
            ref_bytes = (ref_dir / header).read_bytes()
            (lean_dir / header).write_bytes(gen_bytes)
            (abi_dir / header).write_bytes(gen_bytes)
            headers_replaced[header] = {
                "byte_equal": gen_bytes == ref_bytes,
                "sha256": sha256(gen_bytes),
            }

        ref_objs = []
        lean_objs = []
        for unit in sorted(units):
            ref_obj_path = ref_dir / (Path(unit).stem + ".o")
            lean_obj_path = lean_dir / (Path(unit).stem + ".o")
            subprocess.run([cc, *flags, "-fno-ident", "-c", str(ref_dir / unit), "-o", str(ref_obj_path)], cwd=ref_dir, check=True)

            standalone_src = abi_dir / unit
            if standalone_src.is_file():
                standalone_units.append(unit)
                mode = "standalone"
                root, = clang(standalone_src.read_bytes(), flags, abi_dir)
                replaced = [f"{unit}/{name}" for name in sorted(functions(root))]
                skipped = {}
                unlowered = 0
                subprocess.run([cc, *flags, "-fno-ident", "-c", str(standalone_src), "-o", str(lean_obj_path)], cwd=abi_dir, check=True)
            else:
                spliced_units.append(unit)
                mode = "spliced"
                replaced, skipped, unlowered = splice_unit(lean_dir / unit, flags, lean_dir, unit, bodies)
                subprocess.run([cc, *flags, "-fno-ident", "-c", str(lean_dir / unit), "-o", str(lean_obj_path)], cwd=lean_dir, check=True)

            functions_replaced.extend(replaced)
            functions_skipped.update(skipped)
            unlowered_count += unlowered
            ref_objs.append(ref_obj_path)
            lean_objs.append(lean_obj_path)

            ref_obj_bytes = ref_obj_path.read_bytes()
            lean_obj_bytes = lean_obj_path.read_bytes()
            unit_reports[unit] = {
                "mode": mode,
                "replaced_functions": replaced,
                "obj_equal": ref_obj_bytes == lean_obj_bytes,
                "ref_sha256": sha256(ref_obj_bytes),
                "lean_sha256": sha256(lean_obj_bytes),
            }

        ref_archive = ref_dir / "libz.a"
        lean_archive = lean_dir / "libz.a"
        archive_objects(ref_archive, ref_objs)
        archive_objects(lean_archive, lean_objs)

        ref_a_bytes = ref_archive.read_bytes()
        lean_a_bytes = lean_archive.read_bytes()
        out_archive = BUILD / "libz.a"
        shutil.copyfile(lean_archive, out_archive)

    report = {
        "host": platform.platform(),
        "clang": version,
        "target": target,
        "flags": flags,
        "pinned": pinned,
        "abi_layout_verified": True,
        "abi_layout_checks": abi_layout_checks,
        "headers_replaced": headers_replaced,
        "standalone_units": standalone_units,
        "spliced_units": spliced_units,
        "functions_replaced": functions_replaced,
        "functions_skipped": functions_skipped,
        "unlowered_count": unlowered_count,
        "units": unit_reports,
        "archive": {
            "path": "build/libz.a",
            "equal": ref_a_bytes == lean_a_bytes,
            "members_equal": all(u["obj_equal"] for u in unit_reports.values()),
            "ref_sha256": sha256(ref_a_bytes),
            "lean_sha256": sha256(lean_a_bytes),
        },
    }
    (BUILD / "binary-report.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pinned", action="store_true", help="require the pinned compiler, target and C dialect in pins.json")
    args = parser.parse_args()
    result = build_and_verify(args.pinned)

    headers_ok = all(h["byte_equal"] for h in result["headers_replaced"].values())
    obj_ok = sum(1 for u in result["units"].values() if u["obj_equal"])
    total_units = len(result["units"])

    print(f"ABI layouts (_Static_assert): {result['abi_layout_verified']} ({result['abi_layout_checks']})")
    print(f"Headers byte-equal: {sum(h['byte_equal'] for h in result['headers_replaced'].values())}/{len(result['headers_replaced'])}")
    print(f"Standalone 100%-Lean units: {len(result['standalone_units'])}/{total_units} {result['standalone_units']}")
    print(f"Lean functions in .o: {len(result['functions_replaced'])} (skipped: {len(result['functions_skipped'])}, unlowered: {result['unlowered_count']})")
    print(f"Object (.o) byte-identical units: {obj_ok}/{total_units}")
    print(f"Archive build/libz.a byte-identical: {result['archive']['equal']} (sha256={result['archive']['lean_sha256'][:16]}...)")
    print("Report: build/binary-report.json")

    ok = result["abi_layout_verified"] and headers_ok and obj_ok == total_units and result["archive"]["equal"]
    sys.exit(0 if ok else 1)
