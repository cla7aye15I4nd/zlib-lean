# Working in zlib-lean

The maintained scope on branch `dev` is **safety-only** for the patched zlib build identified in [`pins.json`](pins.json), authored directly in a C-like Lean 4 DSL ([`C99/DSL/`](C99/DSL)) whose C emission matches all 15 patched zlib `.o` objects and `libz.a` byte for byte. Do **not** add differential test harnesses or mock filesystems; byte-for-byte binary equality replaces differential testing.

## Safety Documentation & Contracts

- Public API safety contracts live directly on `c_fn` declarations inside `Zlib/*.lean` as Verus-style `requires` / `modifies` / `ensures` clauses, aggregated into [`Zlib.allContracts`](Zlib.lean#L46-L63) and [`Goal.libz_safety`](Zlib/Spec/Safety.lean#L101-L111). Distinguish exclusion of `RunState.ub` (`C99.Sem.Safe`) from bounded termination (`C99.Sem.TerminatesSafely` when `os.readBudget.isSome`).
- Record manual decisions about C undefined behavior in the exception register ([`docs/SAFETY.md#3-manual-undefined-behavior-exceptions`](docs/SAFETY.md#3-manual-undefined-behavior-exceptions)). Cite the operation in both the semantics ([`C99/Semantics.lean`](C99/Semantics.lean)) and the patched C + Lean sources, its exact guard, and the effect on the safety claim. Keep newly discovered discrepancies open until resolved.
- For source comparisons and binary verification, always use the revision and ordered patches in [`pins.json`](pins.json). `make reference` reconstructs patched zlib in `build/reference/` ([`tools/reference.py`](tools/reference.py)).

## Verification Rules

- Always keep [`C99/`](C99.lean) (`AST.lean`, `Mem.lean`, `Libc.lean`, `Semantics.lean`, `EmitC.lean`, `C99.lean`, `DSL/Contract.lean`) 100% zlib-agnostic and within the LOC budgets enforced by [`tools/check_tcb.py`](tools/check_tcb.py).
- Match checks to changes: verify markdown links, Lean declaration names, and Make targets for doc edits; run `make build && make check-api && make check-tcb && make check-kernel` for Lean/DSL/spec edits; run `make binary-equal` (and `make archive-equal` on pinned Linux) whenever C translation or ABI headers change.
