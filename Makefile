PREFIX ?= $(HOME)/.idris2

MAJOR=0
MINOR=2
PATCH=1

export IDRIS2_VERSION := ${MAJOR}.${MINOR}.${PATCH}

.PHONY: all
all: build install-support

.PHONY: install-support
install-support:
	mkdir -p ${PREFIX}/idris2-${IDRIS2_VERSION}/support/ocaml
	install support/* ${PREFIX}/idris2-${IDRIS2_VERSION}/support/ocaml

.PHONY: stop-instances
stop-instances:
	killall -q scheme || true
	killall -q idris2.so || true
	killall -q idris2 || true

.PHONY: build
build: stop-instances
	idris2 --build idris2-ocaml.ipkg