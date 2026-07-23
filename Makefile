TARGET         ?= ./stelf
DUNE_LOCK      ?= ./dune.lock/
OPAM_FILE      ?= ./stelf.opam
DUNE_BUILD_DIR ?= _build/default
DUNE_MIN_VERSION ?= 3.21
DUNE_PROJECT   ?= ./dune-project
SWITCH         ?= .
OPAM           ?= opam
OPAM_EXEC      := $(OPAM) exec --switch $(SWITCH) --
DUNE           ?= dune

SWITCH_SENTINEL := _opam/.opam-switch/switch-config
DUNE_SENTINEL   := _opam/lib/dune/META
DEPS_SENTINEL   := .deps-installed

.PHONY: all build test install docs clean check lock

all: build

# Phase 1: initialize opam if needed, then create the local switch
$(SWITCH_SENTINEL):
	$(OPAM) init --bare --no-setup --yes 2>/dev/null || true
	$(OPAM) switch create $(SWITCH) --empty --yes 2>/dev/null || true
	@test -f $@ || (echo "ERROR: opam switch creation failed"; exit 1)

# Phase 2: install OCaml compiler + dune >= $(DUNE_MIN_VERSION) into the switch
$(DUNE_SENTINEL): $(SWITCH_SENTINEL)
	$(OPAM) install --switch $(SWITCH) --yes \
	    "ocaml>=5.0.0" "dune>=$(DUNE_MIN_VERSION)"

# Phase 3: ensure submodules are present, then generate stelf.opam from dune-project
# dune.lock/ is committed — re-locking is done explicitly via `make lock`
$(OPAM_FILE): $(DUNE_PROJECT) $(DUNE_SENTINEL)
	git submodule update --init --recursive
	$(OPAM_EXEC) $(DUNE) build $(OPAM_FILE)

# Phase 4: install all package dependencies into the local switch
$(DEPS_SENTINEL): $(OPAM_FILE)
	$(OPAM) install --switch $(SWITCH) . --deps-only --yes
	@touch $@

build: $(DEPS_SENTINEL)
	$(OPAM_EXEC) $(DUNE) build
	cp $(DUNE_BUILD_DIR)/bin/main.exe $(TARGET)

test: $(DEPS_SENTINEL)
	$(OPAM_EXEC) $(DUNE) runtest

check: $(DEPS_SENTINEL)
	$(OPAM_EXEC) $(DUNE) build @check

install: build
	$(OPAM_EXEC) $(DUNE) install --prefix _opam

docs: $(DEPS_SENTINEL)
	$(OPAM_EXEC) $(DUNE) build @doc

# Explicitly refresh the lock file (requires network; updates dune.lock/)
lock: $(DUNE_SENTINEL)
	$(OPAM_EXEC) $(DUNE) pkg lock

clean:
	$(OPAM_EXEC) $(DUNE) clean
	rm -f $(TARGET) $(DEPS_SENTINEL)
