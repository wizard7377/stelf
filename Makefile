BUILD_DIR ?= _build/default
DUNE ?= dune
DUNE_PROJECT ?= ./dune-project
DUNE_WORKSPACE ?= ./dune-workspace

.PHONY: all build test docs install clean repl check help

all: build test docs install 

dune.lock/: $(DUNE_PROJECT) $(DUNE_WORKSPACE)
	@$(DUNE) pkg lock
build: dune.lock/
	@$(DUNE) build

check: dune.lock/
	@$(DUNE) build @check

repl: dune.lock/
	@$(DUNE) utop

test: dune.lock/
	@$(DUNE) runtest

docs: dune.lock/
	@$(DUNE) build @doc

install: dune.lock/
	@$(DUNE) install

clean: dune.lock/
	@$(DUNE) clean

