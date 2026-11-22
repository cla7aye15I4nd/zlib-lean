export LEAN_NUM_THREADS ?= 3

.PHONY: audit ast-equal emit reference bytes differential proof test

audit:
	python3 tools/audit.py

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

test:
	python3 -m unittest discover -s tests -p 'test_*.py'
