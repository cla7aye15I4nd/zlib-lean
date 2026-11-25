export LEAN_NUM_THREADS ?= 3
export PATH := $(HOME)/.elan/bin:$(PATH)
LAKE ?= $(shell command -v lake 2>/dev/null || echo $(HOME)/.elan/bin/lake)

.PHONY: build reference emit binary-equal archive-equal archive-equal-compcert check-api check-tcb check-kernel

build:
	$(LAKE) build --wfail C99 C99.Proof Zlib Zlib.Spec.Safety Zlib.Proof lean2c

reference:
	scripts/verify.sh reference build/reference

emit: build
	$(LAKE) exe lean2c emit build/generated

binary-equal: build
	scripts/verify.sh binary

archive-equal: build
	scripts/verify.sh binary --pinned

archive-equal-compcert: build
	scripts/verify.sh binary --compcert

check-api: build
	scripts/verify.sh reference build/reference
	$(LAKE) exe lean2c check-api build/reference/zlib.h

check-tcb: build
	$(LAKE) exe lean2c check-tcb

check-kernel: build
	$(LAKE) env leanchecker --fresh Zlib.Proof
