TARGET         ?= stelf
DUNE_LOCK      ?= ./dune.lock/
OPAM_FILE      ?= ./stelf.opam
DUNE_BUILD_DIR ?= _build/default
# Must match the (dune (>= ...)) constraint in $(DUNE_PROJECT). If this is
# lower, phase 2 installs a dune that cannot build the project at all and the
# failure surfaces much later, as a lang-version error from dune itself.
DUNE_MIN_VERSION ?= 3.24
DUNE_PROJECT   ?= ./dune-project
SWITCH         ?= .
OPAM           ?= opam
OPAM_EXEC      := $(OPAM) exec --switch $(SWITCH) --
DUNE           ?= dune

# Standard GNU-ish install knobs, so packagers can stage into a build root:
#   make install PREFIX=/usr
#   make install DESTDIR=/tmp/stage PREFIX=/usr
PREFIX         ?= $(HOME)/.local
DESTDIR        ?=
# Where `dune build @install` stages the package: bin/, lib/ and doc/, with the
# executable already under its public name.
INSTALL_TREE   ?= _build/install/default

SWITCH_SENTINEL := _opam/.opam-switch/switch-config
DUNE_SENTINEL   := _opam/lib/dune/META
DEPS_SENTINEL   := .deps-installed

.PHONY: all build test install uninstall docs clean check lock js

all: build

# Phase 1: initialize opam if needed, then create the local switch
$(SWITCH_SENTINEL):
	@$(OPAM) init --bare --no-setup --yes 2>/dev/null || true
	@$(OPAM) switch create $(SWITCH) --empty --yes 2>/dev/null || true
	@test -f $@ || (echo "ERROR: opam switch creation failed"; exit 1)

# Phase 2: install OCaml compiler + dune >= $(DUNE_MIN_VERSION) into the switch
$(DUNE_SENTINEL): $(SWITCH_SENTINEL)
	@$(OPAM) install --switch $(SWITCH) --yes \
	    "ocaml>=5.0.0" "dune>=$(DUNE_MIN_VERSION)"

# Phase 3: ensure submodules are present, then generate stelf.opam from dune-project
# dune.lock/ is committed — re-locking is done explicitly via `make lock`
$(OPAM_FILE): $(DUNE_PROJECT) $(DUNE_SENTINEL)
	@git submodule update --init --recursive
	$(OPAM_EXEC) $(DUNE) build $(OPAM_FILE)

# Phase 4: install all package dependencies into the local switch
$(DEPS_SENTINEL): $(OPAM_FILE)
	@$(OPAM) install --switch $(SWITCH) . --deps-only --yes
	@touch $@

# NOT `dune install`: this project uses Dune package management (dune.lock/ is
# committed), and dune refuses `install`/`uninstall` in that mode --
# "dune install is not supported with Dune package management". What it does
# still produce is a complete, correctly-named install tree under
# $(INSTALL_TREE), so copy that.
#
# This replaces a bare `cp ./stelf ~/.local/bin/`, which ignored PREFIX and
# DESTDIR, installed only the executable, failed if the target directory did
# not exist, and had no inverse.
# -L, not plain -a: dune stages the executable as a RELATIVE symlink
# (bin/stelf -> ../../../default/bin/main.exe). Preserving the link would
# install a dangling pointer that resolves to nothing outside _build, so the
# copy must dereference.
install: build
	@$(OPAM_EXEC) $(DUNE) build @install
	@mkdir -p "$(DESTDIR)$(PREFIX)"
	@cp -RL $(INSTALL_TREE)/. "$(DESTDIR)$(PREFIX)/"
	@echo "Installed $(TARGET) to $(DESTDIR)$(PREFIX)/bin/$(TARGET)"

# Removes exactly what `install` places. Kept in sync by hand: the sections
# below are the ones $(INSTALL_TREE) actually contains.
uninstall:
	@rm -f  "$(DESTDIR)$(PREFIX)/bin/$(TARGET)"
	@rm -rf "$(DESTDIR)$(PREFIX)/lib/stelf" "$(DESTDIR)$(PREFIX)/lib/basis"
	@rm -rf "$(DESTDIR)$(PREFIX)/doc/stelf" "$(DESTDIR)$(PREFIX)/doc/basis"
	@echo "Removed $(TARGET) from $(DESTDIR)$(PREFIX)"

# Deliberately NOT dependent on `lock`: dune.lock/ is committed, so a normal
# build must work offline and must not silently move dependency versions.
# Re-locking is explicit, via `make lock`.
build: $(DEPS_SENTINEL)
	$(OPAM_EXEC) $(DUNE) build
	@echo "Copying built executable to $(TARGET)"
	@cp -f $(DUNE_BUILD_DIR)/bin/main.exe ./$(TARGET)

test: $(DEPS_SENTINEL)
	$(OPAM_EXEC) $(DUNE) runtest

check: $(DEPS_SENTINEL)
	$(OPAM_EXEC) $(DUNE) build @check


docs: $(DEPS_SENTINEL)
	$(OPAM_EXEC) $(DUNE) build @doc

# Explicitly refresh the lock file (requires network; updates dune.lock/)
lock: $(DUNE_SENTINEL) $(DUNE_PROJECT)
	@$(OPAM_EXEC) $(DUNE) pkg lock

clean:
	$(OPAM_EXEC) $(DUNE) clean
	@rm -f ./$(TARGET) $(DEPS_SENTINEL)
