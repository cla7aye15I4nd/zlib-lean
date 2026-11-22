export LEAN_NUM_THREADS ?= 3

.PHONY: audit audit-pinned ast-equal emit reference bytes differential proof library-safety test

audit:
	python3 tools/audit.py

audit-pinned:
	python3 tools/audit.py --pinned

ast-equal:
	python3 tools/audit.py --require-equal

emit:
	bin/lean2c emit build/generated

reference:
	python3 tools/reference.py

bytes: reference emit
	bin/lean2c compare build/reference build/generated build/bytes.json

differential:
	python3 tools/differential.py

proof:
	lake build --wfail ZlibF
	lake env leanchecker --fresh ZlibF.Results

library-safety: proof
	python3 tools/check_public_safety.py

test:
	lake build --wfail Lean2C.Lower ZlibF.Proof.LibcMemory
	lake env lean tests/ShiftLowering.lean
	lake env lean -DwarningAsError=true tests/SafetyRules.lean
	python3 -m unittest discover -s tests -p 'test_*.py'
