# ZesuSsz: Islaris verification of the Zesu SSZ decoder.
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
CHECK_LOCAL_BUILD_DIR ?= $(CURDIR)/_build/agents/check-local
CHECK_LOCAL_JOBS ?= 32
CHECK_AGENT ?= push1
AGENT_BUILD_DIR ?= $(CURDIR)/_build/agents/$(CHECK_AGENT)
AGENT_JOBS ?= 32
export AGENT_BUILD_DIR

PROG      ?= entrypoints
LOAD_ADDR ?= 0x10300000

DUMP      := build/endpoint-entry-dump/entrypoints.dump
TRACE_DIR := generated/isla-traces/entrypoints
TRACE_COQ := IslaTraces.entrypoints

ZKVM_EXIT_DUMP      := experiments/islaris-zkvm-exit/zkvm_exit.dump
ZKVM_EXIT_TRACE_DIR := generated/isla-traces/zkvm_exit
ZKVM_EXIT_TRACE_COQ := IslaTraces.zkvm_exit
ZKVM_EXIT_ISLA_CFG  := riscv64_zesu_exit.toml

ALLOCATOR_GET_DUMP      := experiments/islaris-allocator-get/allocator_get.dump
ALLOCATOR_GET_TRACE_DIR := generated/isla-traces/allocator_get
ALLOCATOR_GET_TRACE_COQ := IslaTraces.allocator_get
ALLOCATOR_GET_ISLA_CFG  := riscv64_zesu_allocator.toml

READ_INPUT_DUMP      := experiments/islaris-read-input/read_input.dump
READ_INPUT_TRACE_DIR := generated/isla-traces/read_input
READ_INPUT_TRACE_COQ := IslaTraces.read_input
READ_INPUT_ISLA_CFG  := riscv64_zesu_allocator.toml
WRITE_SUCCESS_DUMP_DIR  := experiments/islaris-write-success/generated
WRITE_SUCCESS_DUMP_STAMP := $(WRITE_SUCCESS_DUMP_DIR)/.stamp
WRITE_SUCCESS_TRACE_STAMP := generated/isla-traces/write_success.stamp
WRITE_SUCCESS_INDEX_DIR := generated/isla-traces/write_success_blocks
WRITE_SUCCESS_INDEX_STAMP := $(WRITE_SUCCESS_INDEX_DIR)/.stamp
WRITE_SUCCESS_ISLA_CFG  := riscv64_zesu_write_success.toml
COQ_DEPS  := InstrSpecs lithium iris stdpp RecordUpdate Ltac2

ISLA_CFG := riscv64_zesu.toml
ISLA_ETC := $(shell opam var --switch=$(OPAM_SWITCH) prefix)/etc/islaris

.PHONY: all
all: proof

# --- pinned target ------------------------------------------------------

.PHONY: target-source
target-source:
	nix run .#link-zesu-source

.PHONY: disasm
disasm: $(DUMP)

$(DUMP):
	mkdir -p build
	nix build .#endpoint-entry-dump --out-link build/endpoint-entry-dump

# --- install the isla config -------------------------------------------
$(ISLA_ETC)/$(ISLA_CFG): ZesuSsz/$(ISLA_CFG)
	install -m644 $< $@

.PHONY: install-isla-config
install-isla-config: $(ISLA_ETC)/$(ISLA_CFG)

# --- generate traces ---------------------------------------------------
$(TRACE_DIR)/instrs.v: $(DUMP) $(ISLA_ETC)/$(ISLA_CFG)
	mkdir -p $(TRACE_DIR)
	$(OPAM) islaris $(DUMP) -j 6 -o $(TRACE_DIR) \
	  --coqdir=$(TRACE_COQ) --arch=riscv64
	sed -i -e '/(package islaris)/d' \
	       -e 's/(theories isla isla.riscv64)/(theories isla isla.riscv64 $(COQ_DEPS))/' \
	       $(TRACE_DIR)/dune

.PHONY: traces
traces: $(TRACE_DIR)/instrs.v $(ZKVM_EXIT_TRACE_DIR)/instrs.v $(ALLOCATOR_GET_TRACE_DIR)/instrs.v $(READ_INPUT_TRACE_DIR)/instrs.v $(WRITE_SUCCESS_TRACE_STAMP) $(WRITE_SUCCESS_INDEX_STAMP)

$(ISLA_ETC)/$(ZKVM_EXIT_ISLA_CFG): experiments/islaris-zkvm-exit/$(ZKVM_EXIT_ISLA_CFG)
	install -m644 $< $@

$(ZKVM_EXIT_TRACE_DIR)/instrs.v: $(ZKVM_EXIT_DUMP) $(ISLA_ETC)/$(ZKVM_EXIT_ISLA_CFG)
	mkdir -p $(ZKVM_EXIT_TRACE_DIR)
	$(OPAM) islaris $(ZKVM_EXIT_DUMP) -j 3 -o $(ZKVM_EXIT_TRACE_DIR) \
	  --coqdir=$(ZKVM_EXIT_TRACE_COQ) --arch=riscv64
	sed -i -e '/(package islaris)/d' \
	       -e 's/(theories isla isla.riscv64)/(theories isla isla.riscv64 $(COQ_DEPS))/' \
	       $(ZKVM_EXIT_TRACE_DIR)/dune

.PHONY: zkvm-exit-traces
zkvm-exit-traces: $(ZKVM_EXIT_TRACE_DIR)/instrs.v

$(ISLA_ETC)/$(ALLOCATOR_GET_ISLA_CFG): experiments/islaris-allocator-get/$(ALLOCATOR_GET_ISLA_CFG)
	install -m644 $< $@

$(ALLOCATOR_GET_TRACE_DIR)/instrs.v: $(ALLOCATOR_GET_DUMP) $(ISLA_ETC)/$(ALLOCATOR_GET_ISLA_CFG)
	mkdir -p $(ALLOCATOR_GET_TRACE_DIR)
	$(OPAM) islaris $(ALLOCATOR_GET_DUMP) -j 8 -o $(ALLOCATOR_GET_TRACE_DIR) \
	  --coqdir=$(ALLOCATOR_GET_TRACE_COQ) --arch=riscv64
	sed -i -e '/(package islaris)/d' \
	       -e 's/(theories isla isla.riscv64)/(theories isla isla.riscv64 $(COQ_DEPS))/' \
	       $(ALLOCATOR_GET_TRACE_DIR)/dune

.PHONY: allocator-get-traces
allocator-get-traces: $(ALLOCATOR_GET_TRACE_DIR)/instrs.v

$(READ_INPUT_TRACE_DIR)/instrs.v: $(READ_INPUT_DUMP) $(ISLA_ETC)/$(READ_INPUT_ISLA_CFG)
	mkdir -p $(READ_INPUT_TRACE_DIR)
	$(OPAM) islaris $(READ_INPUT_DUMP) -j 8 -o $(READ_INPUT_TRACE_DIR) \
	  --coqdir=$(READ_INPUT_TRACE_COQ) --arch=riscv64
	sed -i -e '/(package islaris)/d' \
	       -e 's/(theories isla isla.riscv64)/(theories isla isla.riscv64 $(COQ_DEPS))/' \
	       $(READ_INPUT_TRACE_DIR)/dune

.PHONY: read-input-traces
read-input-traces: $(READ_INPUT_TRACE_DIR)/instrs.v

$(WRITE_SUCCESS_DUMP_STAMP): build/endpoint-elf build/endpoint-cfg experiments/islaris-write-success/profile.json ZesuSsz/Evidence/generate_islaris_dump.py
	$(PYTHON) ZesuSsz/Evidence/generate_islaris_dump.py \
	  --disassembly build/endpoint-elf/meta/disassembly.txt \
	  --cfg build/endpoint-cfg/zesu-cfg.json \
	  --profile experiments/islaris-write-success/profile.json \
	  --split-output-dir $(WRITE_SUCCESS_DUMP_DIR)
	touch $@

$(ISLA_ETC)/$(WRITE_SUCCESS_ISLA_CFG): experiments/islaris-write-success/$(WRITE_SUCCESS_ISLA_CFG)
	install -m644 $< $@

$(WRITE_SUCCESS_TRACE_STAMP): $(WRITE_SUCCESS_DUMP_STAMP) $(ISLA_ETC)/$(WRITE_SUCCESS_ISLA_CFG)
	find generated/isla-traces -maxdepth 1 -type d \
	  -name 'write_success_[0-9]*' -exec rm -rf {} +
	@find $(WRITE_SUCCESS_DUMP_DIR) -maxdepth 1 -type f -name 'block_*.dump' \
	  -print0 | sort -z | xargs -0 -n 1 -P 3 sh -c ' \
	    set -e; \
	    dump_file=$$1; \
	    block_name=$$(basename $$dump_file .dump); \
	    block_number=$${block_name#block_}; \
	    trace_dir=generated/isla-traces/write_success_$$block_number; \
	    mkdir -p $$trace_dir; \
	    $(OPAM) islaris $$dump_file -j 16 -o $$trace_dir \
	      --coqdir=IslaTraces.write_success_$$block_number --arch=riscv64; \
	    sed -i -e "/(package islaris)/d" \
	      -e "s/(theories isla isla.riscv64)/(theories isla isla.riscv64 $(COQ_DEPS))/" \
	      $$trace_dir/dune \
	  ' sh
	touch $@

$(WRITE_SUCCESS_INDEX_STAMP): $(WRITE_SUCCESS_TRACE_STAMP) Makefile ZesuSsz/Evidence/generate_islaris_trace_index.py
	$(PYTHON) ZesuSsz/Evidence/generate_islaris_trace_index.py \
	  --dump-dir $(WRITE_SUCCESS_DUMP_DIR) \
	  --output-dir $(WRITE_SUCCESS_INDEX_DIR) --first-block 9 \
	  --hint-group LoadBlock:0x14d80:0x14e00 \
	  --hint-group ValueBlock:0x14e88:0x14f08 \
	  --hint-group HashesLoop:0x15754:0x158e0 \
	  --hint-group BlobHashesLoop:0x153d4:0x15564 \
	  --hint-group StorageKeysLoop:0x15228:0x153b4 \
	  --hint-group WithdrawalsLoop:0x15694:0x156e8 \
	  --hint-group AuthorizationsLoop:0x15590:0x15620 \
	  --hint-group AccessListsLoop:0x151d4:0x153c0 \
	  --hint-group TransactionsLoop:0x14f00:0x15668
	touch $@

.PHONY: write-success-traces
write-success-traces: $(WRITE_SUCCESS_TRACE_STAMP) $(WRITE_SUCCESS_INDEX_STAMP)

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
	$(OPAM) dune build --root . @all

.PHONY: proof-verbose
proof-verbose: traces
	$(OPAM) dune build --root . @all --display short

# --- housekeeping -------------------------------------------------------
.PHONY: doctor
doctor:
	@bash ZesuSsz/Toolchain/doctor.sh

.PHONY: endpoint
endpoint:
	nix build .#endpoint-elf

build/endpoint-elf:
	mkdir -p build
	nix build .#endpoint-elf --out-link $@

.PHONY: cfg
cfg:
	nix build .#endpoint-cfg

.PHONY: evidence
evidence:
	nix build .#level1-contract-evidence

.PHONY: check-evm-sail-snapshot
check-evm-sail-snapshot:
	$(PYTHON) ZesuSsz/EvmSail/check_snapshot.py

.PHONY: regenerate-evm-sail-snapshot
regenerate-evm-sail-snapshot:
	bash ZesuSsz/EvmSail/regenerate_snapshot.sh

.PHONY: check-evidence-tools
check-evidence-tools:
	PYTHONPATH=ZesuSsz/Evidence $(PYTHON) -m unittest discover -s ZesuSsz/Evidence -p 'test_*.py'
	$(PYTHON) ZesuSsz/Evidence/check_parity.py
	$(PYTHON) ZesuSsz/Evidence/check_proof_hygiene.py
	bash ZesuSsz/Evidence/check_write_success_decoder.sh

.PHONY: check-proof-hygiene
check-proof-hygiene:
	$(PYTHON) ZesuSsz/Evidence/check_proof_hygiene.py

.PHONY: check-fast
check-fast: check-evidence-tools
	$(PYTHON) tools/build_record.py --build-dir $(AGENT_BUILD_DIR) \
	  --target check-fast -- $(OPAM) dune build --root . \
	  --build-dir $(AGENT_BUILD_DIR) --cache=enabled -j$(AGENT_JOBS) \
	  @ZesuSsz/Contracts/all @ZesuSsz/Automation/all \
	  @ZesuSsz/Export/all @ZesuSsz/Compliance/all

.PHONY: check-iris
check-iris:
	$(PYTHON) tools/build_record.py --build-dir $(AGENT_BUILD_DIR) \
	  --target check-iris -- $(OPAM) dune build --root . \
	  --build-dir $(AGENT_BUILD_DIR) --cache=enabled -j$(AGENT_JOBS) \
	  @ZesuSsz/Proofs/all

.PHONY: check-level1-rocq
check-level1-rocq:
	nix build .#level1-contract-rocq

.PHONY: check-evidence-reproducible
check-evidence-reproducible:
	nix build --rebuild .#level1-contract-evidence --no-link

.PHONY: check-viewer
check-viewer:
	$(PYTHON) -m unittest discover -s ZesuSsz/Viewer -p 'test_*.py'

.PHONY: check-local
check-local: check-evm-sail-snapshot check-evidence-tools check-viewer traces
	$(PYTHON) tools/build_record.py --build-dir $(CHECK_LOCAL_BUILD_DIR) \
	  --target check-local -- $(OPAM) dune build --root . \
	  --build-dir $(CHECK_LOCAL_BUILD_DIR) --cache=enabled \
	  -j $(CHECK_LOCAL_JOBS) @all

.PHONY: check
check: doctor check-local
	nix flake check

.PHONY: clean
clean:
	rm -rf build
	$(OPAM) dune clean --root . 2>/dev/null || true

.PHONY: distclean
distclean: clean
	rm -rf $(TRACE_DIR)
