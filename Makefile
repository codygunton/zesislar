# Zesislar: islaris verification of the Zesu SSZ decoder.
#
# Mirrors the structure of islaris-tutorial/Makefile.
# Every path is overridable.
ISLARIS_REPO   ?= $(HOME)/islaris
ISLA_REPO      ?= $(HOME)/isla
ISLA_SNAP_REPO ?= $(HOME)/isla-snapshots
OPAM_SWITCH    ?= $(ISLARIS_REPO)

ZIG        ?= zig
RV_LD      ?= riscv64-elf-ld
RV_OBJDUMP ?= riscv64-elf-objdump
RV_OBJCOPY ?= riscv64-elf-objcopy
PYTHON     ?= python3

export PATH := $(CURDIR)/bin:$(ISLARIS_REPO)/bin:$(PATH)
export ISLA_REPO
export ISLA_SNAP_REPO

OPAM := opam exec --switch=$(OPAM_SWITCH) --

PROG      ?= zesu
LOAD_ADDR ?= 0x10300000

SRC_DIR   := verification-target/$(PROG)
DUMP      := $(SRC_DIR)/$(PROG).dump
TRACE_DIR := generated/isla-traces/$(PROG)
TRACE_COQ := IslaTraces.$(PROG)

COQ_DEPS  := InstrSpecs lithium iris stdpp RecordUpdate Ltac2

ISLA_CFG := riscv64_zesu.toml
ISLA_ETC := $(shell opam var --switch=$(OPAM_SWITCH) prefix)/etc/islaris

.PHONY: all
all: proof

# --- disassemble --------------------------------------------------------
# TODO: add a target to produce the ELF from the Zesu nix build.
# For now, assume the ELF is available and the dump is hand-maintained.

.PHONY: disasm
disasm:
	@echo "TODO: produce $(SRC_DIR)/$(PROG).raw.dump from the ELF"

.PHONY: check-dump
check-dump:
	@echo "TODO: diff annotated dump against fresh objdump"

# --- install the isla config -------------------------------------------
$(ISLA_ETC)/$(ISLA_CFG): ZesislarProofs/$(ISLA_CFG)
	install -m644 $< $@

.PHONY: install-isla-config
install-isla-config: $(ISLA_ETC)/$(ISLA_CFG)

# --- generate traces ---------------------------------------------------
$(TRACE_DIR)/instrs.v: $(DUMP) $(ISLA_ETC)/$(ISLA_CFG)
	mkdir -p $(TRACE_DIR)
	$(OPAM) islaris $(DUMP) -j 4 -o $(TRACE_DIR) \
	  --coqdir=$(TRACE_COQ) --arch=riscv64
	sed -i -e '/(package islaris)/d' \
	       -e 's/(theories isla isla.riscv64)/(theories isla isla.riscv64 $(COQ_DEPS))/' \
	       $(TRACE_DIR)/dune

.PHONY: traces
traces: $(TRACE_DIR)/instrs.v

# --- one-off trace exploration -----------------------------------------
.PHONY: trace-one
trace-one:
	@test -n "$(OP)" || { echo "usage: make trace-one OP=<opcode>"; exit 1; }
	@rev=$$(echo $(OP) | sed 's/../& /g' | tr -d ' \n' | fold -w2 | tac | tr -d '\n'); \
	  echo "# opcode $(OP), bytes reversed: $$rev"; \
	  isla-footprint riscv64.ir -f isla_footprint_no_init \
	    -C $(ISLARIS_REPO)/etc/riscv64_isla_coq.toml \
	    --simplify-registers --tree -s -x -i $$rev $(CONSTR)

.PHONY: regs
regs:
	@grep -oP '^register z\K[A-Za-z_0-9]+ : .*' $(ISLA_SNAP_REPO)/riscv64.ir | sort

# --- build proofs -------------------------------------------------------
.PHONY: proof
proof: traces
	$(OPAM) dune build @all

.PHONY: proof-verbose
proof-verbose: traces
	$(OPAM) dune build @all --display short

# --- housekeeping -------------------------------------------------------
.PHONY: doctor
doctor:
	@echo "TODO: copy doctor.sh from islaris-tutorial and adjust"

.PHONY: clean
clean:
	rm -rf build
	$(OPAM) dune clean 2>/dev/null || true

.PHONY: distclean
distclean: clean
	rm -rf $(TRACE_DIR)
