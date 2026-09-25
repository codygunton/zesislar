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

# The resource guard. Every Dune gate and every batch runs inside one
# 200 GiB cgroup scope, and every `coqc` inside its own 6 GiB scope. On
# 2026-09-20 a gate at 48 jobs times the 6 GiB module limit asked for
# 288 GiB of 251 GiB and the server rebooted. The buildout gate uses
# exactly 24 jobs under the guard.
GUARD ?= $(CURDIR)/tools/resource_guard.sh
GUARD_BATCH = $(if $(wildcard $(GUARD)),$(GUARD) batch,env ZESU_NO_GUARD=1)
GATE_JOBS := $(shell test -x $(GUARD) && $(GUARD) gate-jobs 2>/dev/null || echo 24)
FAST_JOBS := $(shell test -x $(GUARD) && $(GUARD) gate-jobs check-fast 2>/dev/null || echo 48)
# `check-iris` runs alone across agents: it holds /tmp/zesu-gate.lock, and
# every guard holds its launches while the lock is live.
GUARD_LOCKED = $(if $(wildcard $(GUARD)),$(GUARD) locked $(1) --,)

CHECK_LOCAL_BUILD_DIR ?= $(CURDIR)/_build/agents/check-local
CHECK_LOCAL_JOBS ?= $(GATE_JOBS)
CHECK_AGENT ?= infra
AGENT_BUILD_DIR ?= $(CURDIR)/_build/agents/$(CHECK_AGENT)
AGENT_JOBS ?= $(GATE_JOBS)
export AGENT_BUILD_DIR
export AGENT_JOBS

PROG      ?= entrypoints
LOAD_ADDR ?= 0x10300000

DUMP      := build/endpoint-entry-dump/entrypoints.dump
TRACE_DIR := generated/isla-traces/entrypoints
TRACE_COQ := IslaTraces.entrypoints

ZKVM_EXIT_DUMP      := build/islaris-dumps/zkvm_exit.dump
ZKVM_EXIT_TRACE_DIR := generated/isla-traces/zkvm_exit
ZKVM_EXIT_TRACE_COQ := IslaTraces.zkvm_exit

ALLOCATOR_GET_DUMP      := build/islaris-dumps/allocator_get.dump
ALLOCATOR_GET_TRACE_DIR := generated/isla-traces/allocator_get
ALLOCATOR_GET_TRACE_COQ := IslaTraces.allocator_get

READ_INPUT_DUMP      := build/islaris-dumps/read_input.dump
READ_INPUT_TRACE_DIR := generated/isla-traces/read_input
READ_INPUT_TRACE_COQ := IslaTraces.read_input
WRITE_FAILURE_DUMP := build/islaris-dumps/write_failure.dump
WRITE_FAILURE_TRACE_DIR := generated/isla-traces/write_failure
WRITE_FAILURE_TRACE_COQ := IslaTraces.write_failure
MAIN_DUMP      := build/islaris-dumps/main.dump
MAIN_TRACE_DIR := generated/isla-traces/main
MAIN_TRACE_COQ := IslaTraces.main
STARTUP_DUMP      := build/islaris-dumps/startup.dump
STARTUP_TRACE_DIR := generated/isla-traces/startup
STARTUP_TRACE_COQ := IslaTraces.startup

WRITE_SUCCESS_DUMP_DIR  := experiments/islaris-write-success/generated
WRITE_SUCCESS_DUMP_STAMP := $(WRITE_SUCCESS_DUMP_DIR)/.stamp
WRITE_SUCCESS_TRACE_STAMP := generated/isla-traces/write_success.stamp
WRITE_SUCCESS_INDEX_DIR := generated/isla-traces/write_success_blocks
WRITE_SUCCESS_INDEX_STAMP := $(WRITE_SUCCESS_INDEX_DIR)/.stamp
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
ZesuSsz/$(ISLA_CFG): ZesuSsz/Contracts/Machine.v tools/machine_config.py
	$(PYTHON) tools/machine_config.py --config $@

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
traces: $(STARTUP_TRACE_DIR)/instrs.v $(MAIN_TRACE_DIR)/instrs.v $(WRITE_FAILURE_TRACE_DIR)/instrs.v $(ZKVM_EXIT_TRACE_DIR)/instrs.v $(ALLOCATOR_GET_TRACE_DIR)/instrs.v $(READ_INPUT_TRACE_DIR)/instrs.v $(WRITE_SUCCESS_TRACE_STAMP) $(WRITE_SUCCESS_INDEX_STAMP)

$(ZKVM_EXIT_TRACE_DIR)/instrs.v: $(ZKVM_EXIT_DUMP) $(ISLA_ETC)/$(ISLA_CFG)
	mkdir -p $(ZKVM_EXIT_TRACE_DIR)
	$(OPAM) islaris $(ZKVM_EXIT_DUMP) -j 3 -o $(ZKVM_EXIT_TRACE_DIR) \
	  --coqdir=$(ZKVM_EXIT_TRACE_COQ) --arch=riscv64
	sed -i -e '/(package islaris)/d' \
	       -e 's/(theories isla isla.riscv64)/(theories isla isla.riscv64 $(COQ_DEPS))/' \
	       $(ZKVM_EXIT_TRACE_DIR)/dune

.PHONY: zkvm-exit-traces
zkvm-exit-traces: $(ZKVM_EXIT_TRACE_DIR)/instrs.v

$(ALLOCATOR_GET_TRACE_DIR)/instrs.v: $(ALLOCATOR_GET_DUMP) $(ISLA_ETC)/$(ISLA_CFG)
	mkdir -p $(ALLOCATOR_GET_TRACE_DIR)
	$(OPAM) islaris $(ALLOCATOR_GET_DUMP) -j 8 -o $(ALLOCATOR_GET_TRACE_DIR) \
	  --coqdir=$(ALLOCATOR_GET_TRACE_COQ) --arch=riscv64
	sed -i -e '/(package islaris)/d' \
	       -e 's/(theories isla isla.riscv64)/(theories isla isla.riscv64 $(COQ_DEPS))/' \
	       $(ALLOCATOR_GET_TRACE_DIR)/dune

.PHONY: allocator-get-traces
allocator-get-traces: $(ALLOCATOR_GET_TRACE_DIR)/instrs.v

$(READ_INPUT_TRACE_DIR)/instrs.v: $(READ_INPUT_DUMP) $(ISLA_ETC)/$(ISLA_CFG)
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

$(WRITE_SUCCESS_TRACE_STAMP): $(WRITE_SUCCESS_DUMP_STAMP) $(ISLA_ETC)/$(ISLA_CFG)
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

# Startup traces use the pinned dump produced by the Evidence tooling.
.PHONY: startup-traces
startup-traces: $(STARTUP_TRACE_DIR)/instrs.v

$(STARTUP_DUMP): build/endpoint-elf experiments/islaris-startup/profile.json ZesuSsz/Evidence/generate_islaris_dump.py
	$(PYTHON) ZesuSsz/Evidence/generate_islaris_dump.py \
	  --disassembly build/endpoint-elf/meta/disassembly.txt \
	  --profile experiments/islaris-startup/profile.json --output $@

$(STARTUP_TRACE_DIR)/instrs.v: $(STARTUP_DUMP) $(ISLA_ETC)/$(ISLA_CFG)
	mkdir -p $(STARTUP_TRACE_DIR)
	$(OPAM) islaris $(STARTUP_DUMP) -j 3 -o $(STARTUP_TRACE_DIR) \
	  --coqdir=$(STARTUP_TRACE_COQ) --arch=riscv64
	sed -i -e '/(package islaris)/d' \
	  -e 's/(theories isla isla.riscv64)/(theories isla isla.riscv64 $(COQ_DEPS))/' \
	  $(STARTUP_TRACE_DIR)/dune

.PHONY: main-traces
main-traces: $(MAIN_TRACE_DIR)/instrs.v

$(MAIN_DUMP): build/endpoint-elf experiments/islaris-main/profile.json ZesuSsz/Evidence/generate_islaris_dump.py
	$(PYTHON) ZesuSsz/Evidence/generate_islaris_dump.py \
	  --disassembly build/endpoint-elf/meta/disassembly.txt \
	  --profile experiments/islaris-main/profile.json --output $@

$(MAIN_TRACE_DIR)/instrs.v: $(MAIN_DUMP) $(ISLA_ETC)/$(ISLA_CFG)
	mkdir -p $(MAIN_TRACE_DIR)
	$(OPAM) islaris $(MAIN_DUMP) -j16 -o $(MAIN_TRACE_DIR) \
	  --coqdir=$(MAIN_TRACE_COQ) --arch=riscv64
	sed -i -e '/(package islaris)/d' \
	  -e 's/(theories isla isla.riscv64)/(theories isla isla.riscv64 $(COQ_DEPS))/' \
	  $(MAIN_TRACE_DIR)/dune

$(ZKVM_EXIT_DUMP): build/endpoint-elf experiments/islaris-zkvm-exit/profile.json ZesuSsz/Evidence/generate_islaris_dump.py
	$(PYTHON) ZesuSsz/Evidence/generate_islaris_dump.py \
	  --disassembly build/endpoint-elf/meta/disassembly.txt \
	  --profile experiments/islaris-zkvm-exit/profile.json --output $@

$(ALLOCATOR_GET_DUMP): build/endpoint-elf experiments/islaris-allocator-get/profile.json ZesuSsz/Evidence/generate_islaris_dump.py
	$(PYTHON) ZesuSsz/Evidence/generate_islaris_dump.py \
	  --disassembly build/endpoint-elf/meta/disassembly.txt \
	  --profile experiments/islaris-allocator-get/profile.json --output $@

$(READ_INPUT_DUMP): build/endpoint-elf experiments/islaris-read-input/profile.json ZesuSsz/Evidence/generate_islaris_dump.py
	$(PYTHON) ZesuSsz/Evidence/generate_islaris_dump.py \
	  --disassembly build/endpoint-elf/meta/disassembly.txt \
	  --profile experiments/islaris-read-input/profile.json --output $@

$(WRITE_FAILURE_DUMP): build/endpoint-elf experiments/islaris-write-failure/profile.json ZesuSsz/Evidence/generate_islaris_dump.py
	$(PYTHON) ZesuSsz/Evidence/generate_islaris_dump.py \
	  --disassembly build/endpoint-elf/meta/disassembly.txt \
	  --profile experiments/islaris-write-failure/profile.json --output $@

$(WRITE_FAILURE_TRACE_DIR)/instrs.v: $(WRITE_FAILURE_DUMP) $(ISLA_ETC)/$(ISLA_CFG)
	mkdir -p $(WRITE_FAILURE_TRACE_DIR)
	$(OPAM) islaris $(WRITE_FAILURE_DUMP) -j16 -o $(WRITE_FAILURE_TRACE_DIR) \
	  --coqdir=$(WRITE_FAILURE_TRACE_COQ) --arch=riscv64
	sed -i -e '/(package islaris)/d' \
	  -e 's/(theories isla isla.riscv64)/(theories isla isla.riscv64 $(COQ_DEPS))/' \
	  $(WRITE_FAILURE_TRACE_DIR)/dune

.PHONY: write-failure-traces
write-failure-traces: $(WRITE_FAILURE_TRACE_DIR)/instrs.v

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

build/endpoint-cfg:
	mkdir -p build
	nix build .#endpoint-cfg --out-link $@

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
check-evidence-tools: startup-traces
	@echo "uncached checks: machine config, tests, parity, hygiene, spec shapes, decoder"
	$(PYTHON) tools/machine_config.py --check
	$(PYTHON) -m unittest discover -s tools -p 'test_*.py'
	PYTHONPATH=ZesuSsz/Evidence $(PYTHON) -m unittest discover -s ZesuSsz/Evidence -p 'test_*.py'
	$(PYTHON) ZesuSsz/Evidence/check_parity.py
	$(PYTHON) ZesuSsz/Evidence/check_proof_hygiene.py
	$(PYTHON) ZesuSsz/Evidence/check_spec_shapes.py
	bash ZesuSsz/Evidence/check_write_success_decoder.sh

.PHONY: check-proof-hygiene
check-proof-hygiene:
	$(PYTHON) ZesuSsz/Evidence/check_proof_hygiene.py

# The checkers run unconditionally, before any step Dune can satisfy from
# its cache: a cached `check-fast` once reported success while a hygiene
# violation stood for two commits. Every report names this run.
.PHONY: check-fast
check-fast: startup-traces check-evidence-tools
	$(GUARD_BATCH) check-fast -- \
	  $(PYTHON) tools/build_record.py --build-dir $(AGENT_BUILD_DIR) \
	  --target check-fast -- $(OPAM) dune build --root . \
	  --build-dir $(AGENT_BUILD_DIR) --cache=enabled -j$(FAST_JOBS) \
	  @ZesuSsz/Contracts/all @ZesuSsz/Automation/all \
	  @ZesuSsz/Export/all @ZesuSsz/Compliance/all

.PHONY: check-iris
check-iris: startup-traces check-evidence-tools
	$(call GUARD_LOCKED,check-iris) $(GUARD_BATCH) check-iris -- \
	  $(PYTHON) tools/build_record.py --build-dir $(AGENT_BUILD_DIR) \
	  --target check-iris -- $(OPAM) dune build --root . \
	  --build-dir $(AGENT_BUILD_DIR) --cache=enabled -j$(AGENT_JOBS) \
	  @ZesuSsz/Proofs/all

# One gate, alone: `gate.sh` wants the gate lock first, so no new batch
# starts, waits for running job scopes to finish, runs the uncached
# checkers itself, and logs the run.
TARGET ?= check-iris
.PHONY: gate
gate:
	bash tools/det/gate.sh $(TARGET)

# --- the segment harness ------------------------------------------------
#
# The five commands a proof of a straight-line segment needs. Every one of
# them runs inside the resource guard. `docs/ai/plan/AUTOMATION_TOOLS.md`
# is the guide.

DET_BUILD_DIR ?= $(CURDIR)/_build/agents/infra
DET_JOBS := $(shell test -x $(GUARD) && $(GUARD) jobs 2>/dev/null || echo 8)
RULE ?=
ALT ?=

# Where a proof search stops, and why: the residual capture and its class.
#   make probe MODULE=WriteSuccessExactEpilogueSegment.v LEMMA=...
.PHONY: probe
probe:
	@test -n "$(MODULE)" -a -n "$(LEMMA)" || \
	  { echo "usage: make probe MODULE=<file.v> LEMMA=<lemma>"; exit 2; }
	$(GUARD_BATCH) probe -- $(PYTHON) tools/residual/show_probe.py \
	  $(MODULE) $(LEMMA) \
	  --build-dir $(DET_BUILD_DIR)

# The exit boundary of a segment, or its first debt.
#   make infer SET=ZesuSsz/Evidence/det/boundary_set.txt
.PHONY: infer
infer:
	$(GUARD_BATCH) infer -- $(PYTHON) tools/det/infer_boundary.py \
	  --set $(SET) --build-dir $(DET_BUILD_DIR) \
	  $(if $(RULE),--rule $(RULE),) $(if $(ALT),--alt $(ALT),) \
	  --out $(DET_BUILD_DIR)/infer.jsonl

# One segment, from an address range to a probed module.
#   make gen-segment ENTRY=0x156e8 EXIT=0x15744
.PHONY: gen-segment
gen-segment:
	@test -n "$(ENTRY)" -a -n "$(EXIT)" || \
	  { echo "usage: make gen-segment ENTRY=0x… EXIT=0x…"; exit 2; }
	$(GUARD_BATCH) gen-segment -- $(PYTHON) tools/det/segment.py \
	  --entry $(ENTRY) --exit $(EXIT) $(if $(NAME),--name $(NAME),) \
	  --build-dir $(DET_BUILD_DIR) \
	  --spec-out $(DET_BUILD_DIR)/segment.json \
	  --out $(DET_BUILD_DIR)/segment.jsonl

# Regenerate the module of a segment that already has one.
#   make gen-module SET=ZesuSsz/Evidence/det/boundary_set.txt
.PHONY: gen-module
gen-module:
	$(GUARD_BATCH) gen-module -- $(PYTHON) tools/det/gen_segment.py \
	  --set $(SET) --build-dir $(DET_BUILD_DIR) --compile \
	  --report $(DET_BUILD_DIR)/generated.jsonl

# Both baselines, for a commit's automation. IMPORTS adds a module that is
# built but not exported, to size its effect before it is installed.
#   make benchmark COMMIT=HEAD
.PHONY: benchmark
benchmark:
	@test -n "$(COMMIT)" || { echo "usage: make benchmark COMMIT=<sha>"; exit 2; }
	$(GUARD_BATCH) benchmark -- $(PYTHON) tools/residual/benchmark.py \
	  --automation $(COMMIT) \
	  --jobs $(DET_JOBS) $(foreach m,$(IMPORTS),--import $(m))
	$(GUARD_BATCH) benchmark-rule15 -- $(PYTHON) tools/residual/benchmark.py \
	  --automation $(COMMIT) \
	  --set ZesuSsz/Evidence/residuals/benchmark_set_rule15.txt \
	  --name rule15 --jobs $(DET_JOBS) $(foreach m,$(IMPORTS),--import $(m))

# One arm per rule, on both baselines, and the delta table.
#   make bench-rules COMMIT=<sha>
.PHONY: bench-rules
bench-rules:
	$(GUARD_BATCH) bench-rules -- $(PYTHON) tools/det/bench_rules.py \
	  --commit $(if $(COMMIT),$(COMMIT),HEAD) --jobs $(DET_JOBS) \
	  --out $(DET_BUILD_DIR)/bench-rules.md

# What one module costs here against another commit. Row 6's zero-cost
# demonstration for rule set v1.
#   make pass-cost BEFORE=origin/islaris-native
.PHONY: pass-cost
pass-cost:
	$(GUARD_BATCH) pass-cost -- $(PYTHON) tools/det/pass_cost.py \
	  $(if $(BEFORE),--before $(BEFORE),) $(if $(MODULE),--module $(MODULE),) \
	  --jobs $(DET_JOBS)

# Two stored arms, lemma by lemma. Row 6's "zero changed outcomes" is a
# per-lemma claim and a summary cannot show it.
#   make outcomes BEFORE=ccf505e81f85 AFTER=9ebff0c63502-v1
.PHONY: outcomes
outcomes:
	@test -n "$(BEFORE)" -a -n "$(AFTER)" || \
	  { echo "usage: make outcomes BEFORE=<arm> AFTER=<arm>"; exit 2; }
	$(PYTHON) tools/det/outcomes_diff.py $(BEFORE) $(AFTER)

# Hand-written lines per segment, before and after. The primary metric.
#   make handlines BEFORE=<sha>
.PHONY: handlines
handlines:
	$(PYTHON) tools/det/handlines.py \
	  --set ZesuSsz/Evidence/det/boundary_set.txt --before $(BEFORE)

# A chain of segments, junction by junction. The two ends keep their
# frozen predicates; every junction between them is inferred.
#   make chain CHAIN=ZesuSsz/Evidence/det/chain/tail.json
.PHONY: chain
chain:
	@test -n "$(CHAIN)" || { echo "usage: make chain CHAIN=<file.json>"; exit 2; }
	$(GUARD_BATCH) chain -- $(PYTHON) tools/det/chain.py --chain $(CHAIN) \
	  --build-dir $(DET_BUILD_DIR) $(if $(RULE),--rule $(RULE),) \
	  $(if $(ALT),--alt $(ALT),)

# The segment table and the residual classes, from the records on disk.
.PHONY: report
report:
	$(PYTHON) tools/det/report.py

# What the guard has to say: memory, batch peak, kills.
.PHONY: guard-report
guard-report:
	@$(GUARD) report

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
	$(GUARD_BATCH) check-local -- \
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
