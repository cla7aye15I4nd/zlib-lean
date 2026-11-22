#!/usr/bin/env python3
"""Verify baseline equivalence of safety specifications and proved goals against baseline commits.

This checks two properties independently of manual claims:
1. All 124 baseline safety goals (from pruned baseline commit 1eb63fd, matching 85cd20c's
   safety scope) plus `whole_library_safety` (from b442cf6) remain in `ZlibF.Results.proved`,
   `notDone` is empty, and all 99 baseline `required` goals (plus `whole_library_safety`)
   remain in `ZlibF.Results.required`.
2. When git object history for `85cd20c` (and `b442cf6`) is available locally, stripping Lean
   comments/docstrings from the 17 baseline `ZlibF/Spec/Safety/*.lean` files, all
   `ZlibF/Spec/Common/**.lean` files, and core runtime semantics
   (`ZlibF/Runtime/{Space,Monad,Ptr,Schema}.lean`) shows zero code or goal-statement drift,
   and `PublicEntry` / `StreamProtocol` / `Goal.whole_library_safety` in
   `ZlibF/Spec/Safety/WholeLibrary.lean` match `b442cf6` token-for-token.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BASELINE_COMMIT = "85cd20c"
WHOLE_LIBRARY_COMMIT = "b442cf6"

BASELINE_SAFETY_FILES = (
    "ZlibF/Spec/Safety/Back.lean",
    "ZlibF/Spec/Safety/ByteAddress.lean",
    "ZlibF/Spec/Safety/Checksums.lean",
    "ZlibF/Spec/Safety/Copy.lean",
    "ZlibF/Spec/Safety/Domains.lean",
    "ZlibF/Spec/Safety/GzCalls.lean",
    "ZlibF/Spec/Safety/GzRefusal.lean",
    "ZlibF/Spec/Safety/GzSafety.lean",
    "ZlibF/Spec/Safety/Inflate/Fast.lean",
    "ZlibF/Spec/Safety/Inflate/FastOrigin.lean",
    "ZlibF/Spec/Safety/Inflate/Table.lean",
    "ZlibF/Spec/Safety/Initialisation.lean",
    "ZlibF/Spec/Safety/Queries.lean",
    "ZlibF/Spec/Safety/Refusals.lean",
    "ZlibF/Spec/Safety/Sequences.lean",
    "ZlibF/Spec/Safety/Streams.lean",
    "ZlibF/Spec/Safety/Utilities.lean",
)

IMMUTABLE_RUNTIME_FILES = (
    "ZlibF/Runtime/Space.lean",
    "ZlibF/Runtime/Monad.lean",
    "ZlibF/Runtime/Ptr.lean",
    "ZlibF/Runtime/Schema.lean",
)

BASELINE_PROVED_GOALS: tuple[str, ...] = (
    # Stream functions (23)
    "ZlibF.Spec.Public.Goal.deflateBound_safety",
    "ZlibF.Spec.Public.Goal.deflateBound_z_safety",
    "ZlibF.Spec.Public.Goal.deflateEnd_safety",
    "ZlibF.Spec.Public.Goal.deflateGetDictionary_safety",
    "ZlibF.Spec.Public.Goal.deflateParams_safety",
    "ZlibF.Spec.Public.Goal.deflatePending_safety",
    "ZlibF.Spec.Public.Goal.deflatePrime_safety",
    "ZlibF.Spec.Public.Goal.deflateReset_safety",
    "ZlibF.Spec.Public.Goal.deflateSetDictionary_safety",
    "ZlibF.Spec.Public.Goal.deflateSetHeader_safety",
    "ZlibF.Spec.Public.Goal.deflateTune_safety",
    "ZlibF.Spec.Public.Goal.deflateUsed_safety",
    "ZlibF.Spec.Public.Goal.deflate_safety",
    "ZlibF.Spec.Public.Goal.inflateEnd_safety",
    "ZlibF.Spec.Public.Goal.inflateGetDictionary_safety",
    "ZlibF.Spec.Public.Goal.inflateGetHeader_safety",
    "ZlibF.Spec.Public.Goal.inflateMark_safety",
    "ZlibF.Spec.Public.Goal.inflatePrime_safety",
    "ZlibF.Spec.Public.Goal.inflateReset2_safety",
    "ZlibF.Spec.Public.Goal.inflateReset_safety",
    "ZlibF.Spec.Public.Goal.inflateSetDictionary_safety",
    "ZlibF.Spec.Public.Goal.inflateSync_safety",
    "ZlibF.Spec.Public.Goal.inflate_safety",
    # Initialisation functions (4)
    "ZlibF.Spec.Public.Goal.deflateInit2__safety",
    "ZlibF.Spec.Public.Goal.deflateInit__safety",
    "ZlibF.Spec.Public.Goal.inflateInit2__safety",
    "ZlibF.Spec.Public.Goal.inflateInit__safety",
    # Copy functions (2)
    "ZlibF.Spec.Public.Goal.deflateCopy_safety",
    "ZlibF.Spec.Public.Goal.inflateCopy_safety",
    # Query functions (4)
    "ZlibF.Spec.Public.Goal.zlibCompileFlags_safety",
    "ZlibF.Spec.Public.Goal.zlibVersion_safety",
    "ZlibF.Spec.Public.Goal.compressBound",
    "ZlibF.Spec.Public.Goal.compressBound_z",
    # Checksum functions (11)
    "ZlibF.Spec.Public.Goal.adler32_combine64_safety",
    "ZlibF.Spec.Public.Goal.adler32_combine_safety",
    "ZlibF.Spec.Public.Goal.adler32_safety",
    "ZlibF.Spec.Public.Goal.adler32_z_safety",
    "ZlibF.Spec.Public.Goal.crc32_combine64_safety",
    "ZlibF.Spec.Public.Goal.crc32_combine_gen64_safety",
    "ZlibF.Spec.Public.Goal.crc32_combine_gen_safety",
    "ZlibF.Spec.Public.Goal.crc32_combine_op_safety",
    "ZlibF.Spec.Public.Goal.crc32_combine_safety",
    "ZlibF.Spec.Public.Goal.crc32_safety",
    "ZlibF.Spec.Public.Goal.crc32_z_safety",
    # Compress and uncompress (8)
    "ZlibF.Spec.Public.Goal.compress2_safety",
    "ZlibF.Spec.Public.Goal.compress2_z_safety",
    "ZlibF.Spec.Public.Goal.compress_safety",
    "ZlibF.Spec.Public.Goal.compress_z_safety",
    "ZlibF.Spec.Public.Goal.uncompress2_safe",
    "ZlibF.Spec.Public.Goal.uncompress2_z_safe",
    "ZlibF.Spec.Public.Goal.uncompress_safe",
    "ZlibF.Spec.Public.Goal.uncompress_z_safe",
    # Callback decoder (3)
    "ZlibF.Spec.Public.Goal.inflateBackEnd_safety",
    "ZlibF.Spec.Public.Goal.inflateBackInit__safety",
    "ZlibF.Spec.Public.Goal.inflateBack_safety",
    # Gzip file functions (32)
    "ZlibF.Spec.Public.Goal.gzbuffer_safety",
    "ZlibF.Spec.Public.Goal.gzclearerr_safety",
    "ZlibF.Spec.Public.Goal.gzclose_r_safety",
    "ZlibF.Spec.Public.Goal.gzclose_safety",
    "ZlibF.Spec.Public.Goal.gzclose_w_safety",
    "ZlibF.Spec.Public.Goal.gzdirect_safety",
    "ZlibF.Spec.Public.Goal.gzdopen_safety",
    "ZlibF.Spec.Public.Goal.gzeof_safety",
    "ZlibF.Spec.Public.Goal.gzerror_safety",
    "ZlibF.Spec.Public.Goal.gzflush_safety",
    "ZlibF.Spec.Public.Goal.gzfread_safety",
    "ZlibF.Spec.Public.Goal.gzfwrite_safety",
    "ZlibF.Spec.Public.Goal.gzgetc__safety",
    "ZlibF.Spec.Public.Goal.gzgetc_safety",
    "ZlibF.Spec.Public.Goal.gzgets_safety",
    "ZlibF.Spec.Public.Goal.gzoffset64_safety",
    "ZlibF.Spec.Public.Goal.gzoffset_safety",
    "ZlibF.Spec.Public.Goal.gzopen64_safety",
    "ZlibF.Spec.Public.Goal.gzopen_safety",
    "ZlibF.Spec.Public.Goal.gzprintf_safety",
    "ZlibF.Spec.Public.Goal.gzvprintf_safety",
    "ZlibF.Spec.Public.Goal.gzputc_safety",
    "ZlibF.Spec.Public.Goal.gzputs_safety",
    "ZlibF.Spec.Public.Goal.gzread_safety",
    "ZlibF.Spec.Public.Goal.gzrewind_safety",
    "ZlibF.Spec.Public.Goal.gzseek64_safety",
    "ZlibF.Spec.Public.Goal.gzseek_safety",
    "ZlibF.Spec.Public.Goal.gzsetparams_safety",
    "ZlibF.Spec.Public.Goal.gztell64_safety",
    "ZlibF.Spec.Public.Goal.gztell_safety",
    "ZlibF.Spec.Public.Goal.gzungetc_safety",
    "ZlibF.Spec.Public.Goal.gzwrite_safety",
    # Gzip history and non-vacuity (2)
    "ZlibF.Spec.Public.Goal.gz_sequence_nonvacuity",
    "ZlibF.Spec.Public.Goal.gz_sequence_safety",
    # Call sequences (3)
    "ZlibF.Spec.Public.Goal.deflate_sequence_safety",
    "ZlibF.Spec.Public.Goal.inflate_back_sequence_safety",
    "ZlibF.Spec.Public.Goal.inflate_sequence_safety",
    # Refusals (3)
    "ZlibF.Spec.Public.Goal.deflate_refusal",
    "ZlibF.Spec.Public.Goal.inflate_refusal",
    "ZlibF.Spec.Public.Goal.gz_refusal",
    # Initialisation and call domains (4)
    "ZlibF.Spec.Public.Goal.deflate_initialisation_domain",
    "ZlibF.Spec.Public.Goal.inflate_back_initialisation_domain",
    "ZlibF.Spec.Public.Goal.inflateBack_call_domain",
    "ZlibF.Spec.Public.Goal.inflate_initialisation_domain",
    # ByteAddress goals (9)
    "C.ByteAddress.Spec.Goal.address_read_is_pure",
    "C.ByteAddress.Spec.Goal.byte_modifies_preserve_bases",
    "C.ByteAddress.Spec.Goal.byte_stores_preserve_bases",
    "C.ByteAddress.Spec.Goal.every_existing_heap_accepts_layout",
    "C.ByteAddress.Spec.Goal.every_layout_is_representable",
    "C.ByteAddress.Spec.Goal.first_aligned_offset",
    "C.ByteAddress.Spec.Goal.mask_refines_base_plus_offset",
    "C.ByteAddress.Spec.Goal.pointer_advance_preserves_low_bits",
    "C.ByteAddress.Spec.Goal.raw_block_unchanged",
    # Inffast goals (11)
    "Zlib.Inffast.Spec.Goal.fast_safe",
    "Zlib.Inffast.Spec.Goal.step_safe",
    "Zlib.Inffast.Spec.BodyOrigin.Goal.actual_body_preserves_origin",
    "Zlib.Inffast.Spec.CallOrigin.Goal.actual_fast_preserves_origin",
    "Zlib.Inffast.Spec.Origin.Goal.actual_drop_preserves_origin",
    "Zlib.Inffast.Spec.Origin.Goal.actual_pull_preserves_origin",
    "Zlib.Inffast.Spec.Origin.Goal.actual_rollback_preserves_origin",
    "Zlib.Inffast.Spec.Origin.Goal.drop_preserves_origin",
    "Zlib.Inffast.Spec.Origin.Goal.initial_origin",
    "Zlib.Inffast.Spec.Origin.Goal.pull_preserves_origin",
    "Zlib.Inffast.Spec.Origin.Goal.rollback_preserves_origin",
    # Inftrees goals (5)
    "Zlib.Inftrees.Spec.Goal.inflate_table_content",
    "Zlib.Inftrees.Spec.Goal.inflate_table_decoder_safe",
    "Zlib.Inftrees.Spec.Goal.inflate_table_read_extent",
    "Zlib.Inftrees.Spec.RootTable.Goal.constructor_root_bits",
    "Zlib.Inftrees.Spec.Subtable.Goal.constructor_subtable_bits",
)

BASELINE_REQUIRED_GOALS: tuple[str, ...] = BASELINE_PROVED_GOALS[:99]


def strip_lean_comments(text: str) -> str:
    """Remove Lean line (`-- ...`) and nested block (`/- ... -/`, including `/-!...-/`, `/--...-/`) comments.

    String literals (`"..."`) are preserved verbatim so `--` or `/-` inside strings are untouched.
    """
    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_line = False
    in_string = False

    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""

        if in_line:
            if ch == "\n":
                in_line = False
                out.append("\n")
            i += 1
            continue

        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                if block_depth == 0:
                    out.append(" ")
                i += 2
            elif ch == "\n":
                out.append("\n")
                i += 1
            else:
                i += 1
            continue

        if in_string:
            out.append(ch)
            if ch == "\\" and i + 1 < n:
                out.append(text[i + 1])
                i += 2
            elif ch == '"':
                in_string = False
                i += 1
            else:
                i += 1
            continue

        if ch == '"':
            in_string = True
            out.append(ch)
            i += 1
        elif ch == "-" and nxt == "-":
            in_line = True
            out.append(" ")
            i += 2
        elif ch == "/" and nxt == "-":
            block_depth = 1
            i += 2
        else:
            out.append(ch)
            i += 1

    return "".join(out)


def normalize_tokens(code: str) -> str:
    """Normalize whitespace in comment-stripped Lean code."""
    return " ".join(code.split())


_TOP_DECL_START = re.compile(
    r"(?m)^(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?:def|theorem|lemma|structure|inductive|abbrev|class|instance|axiom|opaque|"
    r"section|end|namespace|open|set_option|variable|universe|import|#\w+)\b"
)
_GOAL_DEF_HEADER = re.compile(
    r"^(?:(?:private|protected)\s+)?def\s+((?:[^\s:({]+\.)?Goal\.[^\s:({]+|compressBound(?:_z)?\b)"
)


def extract_goal_defs(stripped_code: str) -> dict[str, str]:
    """Extract normalized `def ...Goal.<name>` declaration bodies from comment-stripped Lean text."""
    lines = stripped_code.splitlines()
    starts: list[tuple[int, str | None]] = []
    for idx, line in enumerate(lines):
        if _TOP_DECL_START.match(line):
            m = _GOAL_DEF_HEADER.match(line)
            starts.append((idx, m.group(1) if m else None))

    goals: dict[str, str] = {}
    for pos, (start_idx, name) in enumerate(starts):
        if name is None:
            continue
        end_idx = starts[pos + 1][0] if pos + 1 < len(starts) else len(lines)
        body = "\n".join(lines[start_idx:end_idx])
        goals[name] = normalize_tokens(body)
    return goals


def extract_named_decl(stripped_code: str, kind_and_name: str) -> str:
    """Extract a top-level declaration starting with `<kind> <name>` until the next top-level command."""
    lines = stripped_code.splitlines()
    starts = [idx for idx, line in enumerate(lines) if _TOP_DECL_START.match(line)]
    pattern = re.compile(rf"^{re.escape(kind_and_name)}\b")
    for pos, start_idx in enumerate(starts):
        if pattern.match(lines[start_idx].strip()):
            end_idx = starts[pos + 1] if pos + 1 < len(starts) else len(lines)
            return normalize_tokens("\n".join(lines[start_idx:end_idx]))
    raise ValueError(f"Declaration {kind_and_name!r} not found")


def _git_has_commit(commit: str) -> bool:
    res = subprocess.run(
        ["git", "cat-file", "-e", f"{commit}^{{commit}}"],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    return res.returncode == 0


def _git_show(commit: str, rel_path: str) -> str:
    res = subprocess.run(
        ["git", "show", f"{commit}:{rel_path}"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return res.stdout


def _git_ls_tree(commit: str, prefix: str) -> list[str]:
    res = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", commit, prefix],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return [line for line in res.stdout.splitlines() if line.endswith(".lean")]


def check_git_baseline() -> list[str]:
    """Compare current working-tree spec and runtime files against baseline git commits."""
    notes: list[str] = []
    if not _git_has_commit(BASELINE_COMMIT):
        notes.append(f"git commit {BASELINE_COMMIT} unavailable; skipping git source diff check")
        return notes

    errors: list[str] = []
    goal_count = 0

    for rel in BASELINE_SAFETY_FILES:
        base_code = strip_lean_comments(_git_show(BASELINE_COMMIT, rel))
        curr_code = strip_lean_comments((ROOT / rel).read_text(encoding="utf-8"))
        base_goals = extract_goal_defs(base_code)
        curr_goals = extract_goal_defs(curr_code)
        if base_goals != curr_goals:
            missing = sorted(set(base_goals) - set(curr_goals))
            added = sorted(set(curr_goals) - set(base_goals))
            changed = sorted(
                k for k in set(base_goals) & set(curr_goals) if base_goals[k] != curr_goals[k]
            )
            errors.append(
                f"{rel}: Goal.* mismatch vs {BASELINE_COMMIT} "
                f"(missing={missing}, added={added}, changed={changed})"
            )
        goal_count += len(base_goals)
        if normalize_tokens(base_code) != normalize_tokens(curr_code):
            errors.append(f"{rel}: non-comment token diff detected vs {BASELINE_COMMIT}")

    common_files = _git_ls_tree(BASELINE_COMMIT, "ZlibF/Spec/Common/")
    for rel in common_files:
        base_code = strip_lean_comments(_git_show(BASELINE_COMMIT, rel))
        curr_path = ROOT / rel
        if not curr_path.exists():
            errors.append(f"{rel}: missing from working tree")
            continue
        curr_code = strip_lean_comments(curr_path.read_text(encoding="utf-8"))
        if normalize_tokens(base_code) != normalize_tokens(curr_code):
            errors.append(f"{rel}: non-comment diff detected vs {BASELINE_COMMIT}")

    for rel in IMMUTABLE_RUNTIME_FILES:
        base_code = strip_lean_comments(_git_show(BASELINE_COMMIT, rel))
        curr_code = strip_lean_comments((ROOT / rel).read_text(encoding="utf-8"))
        if normalize_tokens(base_code) != normalize_tokens(curr_code):
            errors.append(f"{rel}: non-comment diff detected vs {BASELINE_COMMIT}")

    if _git_has_commit(WHOLE_LIBRARY_COMMIT):
        wl_rel = "ZlibF/Spec/Safety/WholeLibrary.lean"
        base_wl = strip_lean_comments(_git_show(WHOLE_LIBRARY_COMMIT, wl_rel))
        curr_wl = strip_lean_comments((ROOT / wl_rel).read_text(encoding="utf-8"))
        for decl in ("inductive PublicEntry", "inductive StreamProtocol", "def Goal.whole_library_safety"):
            if extract_named_decl(base_wl, decl) != extract_named_decl(curr_wl, decl):
                errors.append(f"{wl_rel}: `{decl}` changed vs {WHOLE_LIBRARY_COMMIT}")

    if errors:
        raise AssertionError("\n".join(errors))

    notes.append(
        f"git baseline verified against {BASELINE_COMMIT}: "
        f"{len(BASELINE_SAFETY_FILES)} safety spec files ({goal_count} Goal.* decls), "
        f"{len(common_files)} Spec/Common files, {len(IMMUTABLE_RUNTIME_FILES)} core Runtime files unchanged"
    )
    return notes


def check_results_registry() -> None:
    """Verify compiled `ZlibF.Results` contains all baseline proved and required goals."""
    assert len(BASELINE_PROVED_GOALS) == 124, len(BASELINE_PROVED_GOALS)
    assert len(BASELINE_REQUIRED_GOALS) == 99, len(BASELINE_REQUIRED_GOALS)

    proved_lit = ", ".join(f"``{n}" for n in BASELINE_PROVED_GOALS)
    req_lit = ", ".join(f"``{n}" for n in BASELINE_REQUIRED_GOALS)
    lean_script = f"""import ZlibF.Results

open Lean Elab Command

#eval show CommandElabM Unit from do
  let baselineProved : List Name := [{proved_lit}]
  let baselineRequired : List Name := [{req_lit}]
  let provedNames := ZlibF.Results.proved.map Prod.fst
  for g in baselineProved do
    if !(provedNames.contains g) then
      throwError "missing baseline proved goal {{g}}"
  if !(provedNames.contains ``ZlibF.Spec.Public.Goal.whole_library_safety) then
    throwError "missing ZlibF.Spec.Public.Goal.whole_library_safety in ZlibF.Results.proved"
  if !ZlibF.Results.notDone.isEmpty then
    throwError "ZlibF.Results.notDone is non-empty: {{ZlibF.Results.notDone}}"
  for g in baselineRequired do
    if !(ZlibF.Results.required.contains g) then
      throwError "missing baseline required goal {{g}}"
  if !(ZlibF.Results.required.contains ``ZlibF.Spec.Public.Goal.whole_library_safety) then
    throwError "missing ZlibF.Spec.Public.Goal.whole_library_safety in ZlibF.Results.required"
  IO.println s!"Results registry retains all {{baselineProved.length}} baseline proved goals (+ whole_library_safety) and {{baselineRequired.length}} baseline required goals (+ whole_library_safety)."
"""
    res = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        cwd=ROOT,
        input=lean_script,
        capture_output=True,
        text=True,
    )
    if res.returncode != 0:
        raise RuntimeError(
            f"Lean registry equivalence check failed (exit {res.returncode}):\n"
            f"{res.stdout}\n{res.stderr}"
        )
    if res.stdout.strip():
        print(res.stdout.strip())


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-lean", action="store_true", help="Skip compiled ZlibF.Results check")
    parser.add_argument("--skip-git", action="store_true", help="Skip git commit comparison")
    args = parser.parse_args(argv)

    if not args.skip_git:
        for note in check_git_baseline():
            print(note)
    if not args.skip_lean:
        check_results_registry()
    return 0


if __name__ == "__main__":
    sys.exit(main())
