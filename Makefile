export LEAN_NUM_THREADS ?= 3

.PHONY: audit audit-pinned archive-equal ast-equal binary binary-pinned emit reference bytes differential proof test

audit:
	python3 tools/audit.py

audit-pinned:
	python3 tools/audit.py --pinned

archive-equal:
	python3 tools/archive.py

ast-equal:
	python3 tools/audit.py --require-equal

binary:
	python3 tools/binary_audit.py

binary-pinned:
	python3 tools/binary_audit.py --pinned

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

test:
	lake env lean tests/ShiftLowering.lean
	python3 -m unittest discover -s tests -p 'test_*.py'
