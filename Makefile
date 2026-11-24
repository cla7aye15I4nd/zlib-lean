export LEAN_NUM_THREADS ?= 3
export PATH := $(HOME)/.elan/bin:$(PATH)
LAKE ?= $(shell command -v lake 2>/dev/null || echo $(HOME)/.elan/bin/lake)

.PHONY: build reference emit binary-equal archive-equal archive-equal-compcert check-api check-tcb check-kernel

build:
	$(LAKE) build --wfail C99 Zlib Zlib.Spec.Safety lean2c

reference:
	python3 tools/reference.py

emit:
	bin/lean2c emit build/generated

binary-equal:
	python3 tools/verify_binary.py

archive-equal:
	python3 tools/archive.py --pinned

archive-equal-compcert:
	python3 tools/archive.py --compcert

check-api:
	python3 tools/check_public_api.py

check-tcb:
	python3 tools/check_tcb.py

check-kernel: build
	$(LAKE) env leanchecker --fresh Zlib.Spec.Safety
