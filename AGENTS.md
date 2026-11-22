# Working in zlib-lean

The maintained verification scope is safety for the patched zlib build identified in `pins.json`. Tie a public claim to a Lean goal, its caller and platform assumptions, and any applicable UB exception. The oss-proof import includes functional lemmas and round-trip theorems. Some safety proofs import shared definitions from functional modules. Directory names alone are insufficient grounds to remove a dependency. [Safety scope](docs/en/trusted-base.md) · [Proof registry](ZlibF/Results.lean)

## Safety documentation

- To document a function, use its `safety_goal` in the API inventory. Read the statement in `ZlibF/Spec/`, follow any common predicates, and check its entry in `ZlibF/Results.lean`. In particular, distinguish exclusion of `Fault.ub` from a proof of return when a goal admits `Fault.outOfFuel`. [API inventory](tests/public-api.json)
- Record manual decisions about C undefined behavior in the exception register. Cite the operation in both the runtime and the patched source, its exact guard and the effect on the safety claim. Keep a newly discovered discrepancy open until its scope and disposition are understood. [Exception register](docs/en/model-limits.md)
- For source comparisons, use the revision and ordered patches in the pins. `make reference` reconstructs them in `build/reference/`. Use the upstream proof documentation at the pinned proof commit when explaining inherited results. [Pins](pins.json) · [Reference reconstruction](tools/reference.py)

## Working alongside proof and translator changes

For a documentation task, edit the README, the relevant page under `docs/`, or these instructions. Check the current diff before touching a shared file. Leave changes to theorem statements, runtime semantics, extraction, and CI to the task that owns them. If the documentation exposes a mismatch, name the affected definition or command so the implementation change can be made separately.

Match the check to the change. Verify documentation links, Lean declaration names and Make targets for prose edits. For proof changes, `make proof` builds and replays the registry. For translation changes, `make audit` reports Clang AST comparisons and `make differential` compares outputs on test inputs. Report each result with its scope. [Commands](README.md#run-the-comparison)
