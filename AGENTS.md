# Working in zlib-lean

The maintained verification scope is **safety-only** for the patched zlib build identified in `pins.json`. Unreachable non-safety modules have been pruned from `ZlibF/`, and `ZlibF/Results.lean` registers and checks safety goals (`ZlibF.Spec.Safety.*`, plus `compressBound` / `compressBound_z`) only. Some safety proofs still reuse internal lemmas from retained `Spec/Functional` modules; directory names alone are insufficient grounds to remove a dependency. [Safety claim and TCB](docs/SAFETY.md) · [Proof registry](ZlibF/Results.lean)

## Safety documentation

- To document a function, use its `safety_goal` in the API inventory. Read the statement in `ZlibF/Spec/`, follow any common predicates, and check its entry in `ZlibF/Results.lean`. Distinguish exclusion of `Fault.ub` from a proof of return when a goal admits `Fault.outOfFuel`. [API inventory](tests/public-api.json)
- Record manual decisions about C undefined behavior in the exception register. Cite the operation in both the runtime and the patched source, its exact guard, and the effect on the safety claim. Keep a newly discovered discrepancy open until its scope and disposition are understood. [Exception register](docs/SAFETY.md#3-manual-undefined-behavior-exceptions)
- For source comparisons, use the revision and ordered patches in the pins. `make reference` reconstructs them in `build/reference/`. [Pins](pins.json) · [Reference reconstruction](tools/reference.py)

## Working alongside proof and translator changes

For a documentation task, edit the README, [docs/SAFETY.md](docs/SAFETY.md), or these instructions. Check the current diff before touching a shared file. Leave changes to theorem statements, runtime semantics, extraction, and CI to the task that owns them. If the documentation exposes a mismatch, name the affected definition or command so the implementation change can be made separately.

Match the check to the change. Verify documentation links, Lean declaration names, and Make targets for prose edits. For proof changes, `make proof` builds and replays the safety registry. For translation or binary integration changes, run `make binary`, `make audit`, `make test`, and `make differential`. Report each result with its scope. [Commands](README.md#commands)
