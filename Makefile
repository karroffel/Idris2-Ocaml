PREFIX ?= $(HOME)/.idris2
IDRIS2 ?= idris2

# IDRIS2_SOURCE_PATH =

MAJOR=0
MINOR=2
PATCH=1

CFLAGS = -fPIE -Wno-pointer-sign -Wno-discarded-qualifiers

export IDRIS2_VERSION := ${MAJOR}.${MINOR}.${PATCH}

.PHONY: all
all: build install-support

.PHONY: support
support:
	cd support/ && cc $(CFLAGS) -O2 -c ocaml_rts.c -I `ocamlc -where` -I ../$(IDRIS2_SOURCE_PATH)/support/c/

.PHONY: install-support
install-support: support
	mkdir -p ${PREFIX}/idris2-${IDRIS2_VERSION}/support/ocaml
	install support/ocaml_rts.o ${PREFIX}/idris2-${IDRIS2_VERSION}/support/ocaml
	install support/OcamlRts.ml ${PREFIX}/idris2-${IDRIS2_VERSION}/support/ocaml

.PHONY: stop-instances
stop-instances:
	killall -q scheme || true
	killall -q idris2.so || true
	killall -q idris2 || true

.PHONY: build
build: stop-instances
	$(IDRIS2) --build idris2-ocaml.ipkg
