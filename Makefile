FLAGS += 
DUNE ?= dune
OPAM ?= opam
SRCS=
OUTPUT_DIR ?= _build 
OUTPUT ?= build

.PHONY: default run build test fmt install check docs
default: install

check: dune dune-project dune-workspace $(SRCS)
	@$(DUNE) build --profile=check 
	@cp $(OUTPUT_DIR)/default/bin/main.exe $(OUTPUT)/stelf.exe
build: dune dune-project dune-workspace $(SRCS)
	@mkdir -p $(OUTPUT)
	@$(DUNE) build --profile=release
	@cp $(OUTPUT_DIR)/default/bin/main.exe $(OUTPUT)/stelf.exe
test: dune dune-project dune-workspace $(SRCS)
	@$(DUNE) build --profile=dev @runtest --force
fmt: dune dune-project dune-workspace $(SRCS)
	@$(DUNE) fmt 


install: build-release 
	@$(DUNE) build @install
	@$(DUNE) install