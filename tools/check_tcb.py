"""Audit Trusted Computing Base cleanliness, zero sorry/axiom, zlib independence, and LOC budgets."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]

CORE_TCB_FILES = [
    "C99/AST.lean",
    "C99/Mem.lean",
    "C99/Libc.lean",
    "C99/Semantics.lean",
    "C99/EmitC.lean",
    "C99.lean",
]
CORE_CONTRACT_FILES = ["C99/DSL/Contract.lean"]
SPEC_FILES = ["Zlib/Spec/Memory.lean", "Zlib/Spec/Safety.lean"]

MAX_CORE_TCB_LOC = 2300
MAX_SPEC_LOC = 500

FORBIDDEN_ZLIB_TOKENS = [
    "z_stream",
    "deflate",
    "inflate",
    "adler32",
    "crc32",
    "gzFile",
    "gz_header",
    "zlib",
    "ZLIB",
    "Z_OK",
    "Z_STREAM_ERROR",
]


def strip_lean_comments_and_strings(text: str) -> str:
    """Replace comments (`--`, nested `/- -/`) and string/char literals with spaces."""
    out = []
    i = 0
    n = len(text)
    block_depth = 0
    in_line = False
    in_str = False
    in_chr = False
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if in_line:
            if ch == "\n":
                in_line = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
        elif block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.extend([" ", " "])
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                out.extend([" ", " "])
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
        elif in_str:
            if ch == "\\" and i + 1 < n:
                out.extend([" ", " "])
                i += 2
            elif ch == '"':
                in_str = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
        elif in_chr:
            if ch == "\\" and i + 1 < n:
                out.extend([" ", " "])
                i += 2
            elif ch == "'":
                in_chr = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
        else:
            if ch == "-" and nxt == "-":
                in_line = True
                out.extend([" ", " "])
                i += 2
            elif ch == "/" and nxt == "-":
                block_depth = 1
                out.extend([" ", " "])
                i += 2
            elif ch == '"':
                in_str = True
                out.append(" ")
                i += 1
            elif ch == "'" and i + 2 < n and (text[i + 1] == "\\" or text[i + 2] == "'"):
                in_chr = True
                out.append(" ")
                i += 1
            else:
                out.append(ch)
                i += 1
    return "".join(out)


def strip_lean_comments(text: str) -> str:
    """Strip `--` and nested `/- -/` comments while keeping code and string literals."""
    out = []
    i = 0
    n = len(text)
    block_depth = 0
    in_line = False
    in_str = False
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if in_line:
            if ch == "\n":
                in_line = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
        elif block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.extend([" ", " "])
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                out.extend([" ", " "])
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
        elif in_str:
            if ch == "\\" and i + 1 < n:
                out.extend([ch, nxt])
                i += 2
            else:
                if ch == '"':
                    in_str = False
                out.append(ch)
                i += 1
        else:
            if ch == "-" and nxt == "-":
                in_line = True
                out.extend([" ", " "])
                i += 2
            elif ch == "/" and nxt == "-":
                block_depth = 1
                out.extend([" ", " "])
                i += 2
            elif ch == '"':
                in_str = True
                out.append(ch)
                i += 1
            else:
                out.append(ch)
                i += 1
    return "".join(out)


def count_lines(rel_path: str) -> int:
    return len((ROOT / rel_path).read_text().splitlines())


def iter_lean_files():
    files = []
    for folder in ("C99", "Zlib"):
        files.extend(sorted((ROOT / folder).rglob("*.lean")))
    for single in ("Zlib.lean", "Main.lean"):
        files.append(ROOT / single)
    return files


def main():
    sorry_hits = []
    axiom_hits = []
    for path in iter_lean_files():
        stripped = strip_lean_comments_and_strings(path.read_text())
        for idx, line in enumerate(stripped.splitlines(), 1):
            if re.search(r"\bsorry\b", line):
                sorry_hits.append(f"{path.relative_to(ROOT)}:{idx}")
            if re.search(r"\baxiom\b", line):
                axiom_hits.append(f"{path.relative_to(ROOT)}:{idx}")
    if sorry_hits:
        raise AssertionError(f"Found `sorry` in: {sorry_hits}")
    if axiom_hits:
        raise AssertionError(f"Found `axiom` in: {axiom_hits}")

    zlib_leaks = []
    token_re = re.compile(r"\b(" + "|".join(re.escape(t) for t in FORBIDDEN_ZLIB_TOKENS) + r")\b")
    for rel in CORE_TCB_FILES + CORE_CONTRACT_FILES:
        text = strip_lean_comments((ROOT / rel).read_text())
        for idx, line in enumerate(text.splitlines(), 1):
            m = token_re.search(line)
            if m:
                zlib_leaks.append(f"{rel}:{idx} ({m.group(1)})")
    if zlib_leaks:
        raise AssertionError(f"Found zlib-specific identifier in Core TCB: {zlib_leaks}")

    core_loc = sum(count_lines(p) for p in CORE_TCB_FILES)
    contract_loc = sum(count_lines(p) for p in CORE_CONTRACT_FILES)
    spec_loc = sum(count_lines(p) for p in SPEC_FILES)
    dsl_loc = sum(
        len(p.read_text().splitlines())
        for p in sorted((ROOT / "C99" / "DSL").glob("*.lean"))
        if str(p.relative_to(ROOT)) not in CORE_CONTRACT_FILES
    )
    zlib_tus_loc = sum(
        len(p.read_text().splitlines())
        for p in sorted((ROOT / "Zlib").rglob("*.lean"))
        if "Zlib/Spec/" not in str(p.relative_to(ROOT))
    )

    if core_loc > MAX_CORE_TCB_LOC:
        raise AssertionError(f"Core TCB LOC {core_loc} exceeds budget {MAX_CORE_TCB_LOC}")
    if spec_loc > MAX_SPEC_LOC:
        raise AssertionError(f"Zlib/Spec LOC {spec_loc} exceeds budget {MAX_SPEC_LOC}")

    print("TCB & Cleanliness Audit Summary:")
    print(f"  Core C99 TCB (AST, Mem, Libc, Semantics, EmitC, C99): {core_loc} LOC (limit {MAX_CORE_TCB_LOC})")
    print(f"  Verus Contract Interface (C99/DSL/Contract):          {contract_loc} LOC")
    print(f"  C-like DSL Frontend (C99/DSL/*):                      {dsl_loc} LOC")
    print(f"  Safety-Only Spec (Zlib/Spec/*):                       {spec_loc} LOC (limit {MAX_SPEC_LOC})")
    print(f"  Zlib C-like Translation Units + Headers + Tables:     {zlib_tus_loc} LOC")
    print("  Cleanliness: 0 sorry, 0 axiom, 0 zlib identifiers in Core TCB.")


if __name__ == "__main__":
    main()
