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
CHECK_LOCAL_JOBS ?= $(AGENT_JOBS)
CHECK_AGENT ?= infra
AGENT_BUILD_DIR ?= $(CURDIR)/_build/agents/$(CHECK_AGENT)
AGENT_JOBS ?= $(GATE_JOBS)
export AGENT_BUILD_DIR
export AGENT_JOBS

STOCK_DIR ?= build/stock-zisk
STOCK_ELF ?= $(STOCK_DIR)/zesu-zisk.elf
STOCK_MANIFEST ?= $(STOCK_DIR)/build-recipe.json
STOCK_CFG ?= $(STOCK_DIR)/cfg.json
PROG ?= decodeItem
DUMP ?= $(STOCK_DIR)/$(PROG).raw.dump
TRACE_DIR ?= generated/isla-traces/stock-zisk/$(PROG)
TRACE_COQ ?= ZesuSsz.Stock.DecodeItem
TRACE_JOBS ?= 6

ISLA_CFG := riscv64_zesu.toml
STOCK_SNAPSHOT ?= $(STOCK_DIR)/platform/riscv64-zisk.ir

.PHONY: all
all: proof

# --- pinned target ------------------------------------------------------

# The stock manifest checks the pinned sources, ELF, and derived reports.
.PHONY: stock-check disasm cfg endpoint
stock-check:
	$(PYTHON) tools/stock_zisk/build.py --check --out $(STOCK_DIR)

disasm cfg endpoint: stock-check

# Generate traces with the selected platform snapshot and config.
STOCK_TRACE_DRIVER ?= tools/stock_zisk/platform/traces.py
.PHONY: traces traces-closure
traces: stock-check
	@test -f "$(STOCK_TRACE_DRIVER)" || { echo "The stock trace driver is absent: $(STOCK_TRACE_DRIVER)"; exit 2; }
	$(PYTHON) $(STOCK_TRACE_DRIVER) --manifest $(STOCK_MANIFEST) \
	  --dump $(DUMP) --out $(TRACE_DIR) --coqdir $(TRACE_COQ) --jobs $(TRACE_JOBS)

traces-closure: stock-check
	$(PYTHON) $(STOCK_TRACE_DRIVER) --manifest $(STOCK_MANIFEST) \
	  --closure --out $(TRACE_DIR) --coqdir $(TRACE_COQ) --jobs $(TRACE_JOBS)

# --- one-off trace exploration -----------------------------------------
.PHONY: trace-one
trace-one: stock-check
	@test -n "$(OP)" || { echo "usage: make trace-one OP=<opcode>"; exit 1; }
	@rev=$$(echo $(OP) | sed 's/../& /g' | tr -d ' \n' | fold -w2 | tac | tr -d '\n'); \
	  echo "# opcode $(OP), bytes reversed: $$rev"; \
	  isla-footprint $(STOCK_SNAPSHOT) -f isla_footprint_no_init \
	    -C ZesuSsz/$(ISLA_CFG) \
	    --simplify-registers --tree -s -x -i $$rev $(CONSTR)

.PHONY: regs
regs:
	@grep -oP '^register z\K[A-Za-z_0-9]+ : .*' $(STOCK_SNAPSHOT) | sort

# --- build proofs -------------------------------------------------------
.PHONY: proof
proof: check-local

.PHONY: proof-verbose
proof-verbose:
	$(OPAM) dune build --root . --build-dir $(AGENT_BUILD_DIR) --cache=enabled -j$(AGENT_JOBS) @all --display short

# --- housekeeping -------------------------------------------------------
.PHONY: doctor
doctor:
	@bash ZesuSsz/Toolchain/doctor.sh

.PHONY: check-evm-sail-snapshot
check-evm-sail-snapshot:
	$(PYTHON) ZesuSsz/EvmSail/check_snapshot.py

.PHONY: regenerate-evm-sail-snapshot
regenerate-evm-sail-snapshot:
	bash ZesuSsz/EvmSail/regenerate_snapshot.sh

.PHONY: check-evidence-tools
check-evidence-tools:
	@echo "uncached checks: machine config, tests, hygiene, spec shapes"
	$(PYTHON) tools/machine_config.py --check
	$(PYTHON) -m unittest discover -s tools -p 'test_*.py'
	PYTHONPATH=ZesuSsz/Evidence $(PYTHON) -m unittest discover -s ZesuSsz/Evidence -p 'test_*.py'
	$(PYTHON) ZesuSsz/Evidence/check_proof_hygiene.py
	$(PYTHON) ZesuSsz/Evidence/check_spec_shapes.py
	$(PYTHON) tools/check_sail_host_axioms.py

.PHONY: check-proof-hygiene
check-proof-hygiene:
	$(PYTHON) ZesuSsz/Evidence/check_proof_hygiene.py

# The checkers run unconditionally, before any step Dune can satisfy from
# its cache: a cached `check-fast` once reported success while a hygiene
# violation stood for two commits. Every report names this run.
#
# Retained production targets (P0-B). `check-fast` builds exactly these
# Dune aliases, after the uncached Python checks of `check-evidence-tools`
# (machine config, tools and Evidence unit tests, hygiene, spec shapes).
# InstrSpecs, ZesuMachineMap, EvmSail and SailStdpp build as dependencies.
# Native index datasets must exist before retained Dune targets start.
RETAINED_TARGETS := \
  @ZesuSsz/Contracts/all \
  @ZesuSsz/Automation/all \
  @ZesuSsz/Export/all \
  @ZesuSsz/Compliance/all \
  @ZesuSsz/Proofs/Tests/all \
  @ZesuSsz/Tests/all
.PHONY: check-fast
check-fast: stock-native-indexes check-evidence-tools check-signatures
	$(GUARD_BATCH) check-fast -- \
	  $(PYTHON) tools/build_record.py --build-dir $(AGENT_BUILD_DIR) \
	  --target check-fast -- $(OPAM) dune build --root . \
	  --build-dir $(AGENT_BUILD_DIR) --cache=enabled -j$(FAST_JOBS) \
	  $(RETAINED_TARGETS)

.PHONY: check-signatures
check-signatures:
	$(OPAM) dune build --root . --build-dir $(AGENT_BUILD_DIR) \
	  --cache=enabled -j$(FAST_JOBS) @install \
	  ZesuSsz/Evidence/SignatureGateFixtures.vo \
	  ZesuSsz/Evidence/PendingParentHeaderSignatureFixtures.vo \
	  ZesuSsz/Evidence/ParentHeaderDifferential.vo

.PHONY: check-iris
check-iris: stock-native-indexes check-evidence-tools
	$(call GUARD_LOCKED,check-iris) $(GUARD_BATCH) check-iris -- \
	  $(PYTHON) tools/build_record.py --build-dir $(AGENT_BUILD_DIR) \
	  --target check-iris -- $(OPAM) dune build --root . \
	  --build-dir $(AGENT_BUILD_DIR) --cache=enabled -j$(AGENT_JOBS) \
	  @all

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

# Run each selected stock CFG block with its entry state.
BLOCK_BUILD_DIR ?= $(AGENT_BUILD_DIR)
BLOCK_CFG ?= $(STOCK_CFG)
BLOCK_FUNCTION ?= rlp.decodeItem
BLOCK_PROOF_DIR ?= $(if $(STATES),$(STATES),ZesuSsz/Proofs/DecodeItem)
BLOCK_TRACE_IMPORT ?= $(TRACE_COQ).instrs
BLOCK_ENTRIES ?= $(STOCK_DIR)/block_entries.json
RULES ?= v2
CAP ?= 600
BLOCK_JOBS ?= $(AGENT_JOBS)
BLOCK_PREPARE_JOBS ?= $(AGENT_JOBS)
.PHONY: block-run block-prepare block-entries
block-entries:
	$(PYTHON) tools/block/entries.py --cfg $(BLOCK_CFG) --function $(BLOCK_FUNCTION) \
	  --proof-dir $(BLOCK_PROOF_DIR) --output $(BLOCK_ENTRIES)

block-prepare: block-entries
	mkdir -p $(BLOCK_BUILD_DIR)
	unset ARISTOTLE_API_KEY OPEN_ROUTER_API_KEY PROVER_API_KEY; \
	  ZESU_MAX_COQC=40 $(GUARD_BATCH) worker-build-2-block-prepare -- $(PYTHON) tools/build_record.py \
	  --build-dir $(BLOCK_BUILD_DIR) --target block-prepare -- $(OPAM) dune build --root . \
	  --build-dir $(BLOCK_BUILD_DIR) --cache=enabled -j$(BLOCK_PREPARE_JOBS) @ZesuSsz/Automation/all \
	  ZesuSsz/Automation/Sets/v2.vo $(if $(wildcard ZesuSsz/Automation/Sets/call.v),ZesuSsz/Automation/Sets/call.vo,) \
	  $$($(PYTHON) tools/block/entries.py --targets --output $(BLOCK_ENTRIES) --proof-dir $(BLOCK_PROOF_DIR)) $(if $(IMPORT_MODULE),$(subst .,/,$(IMPORT_MODULE)).vo,)

block-run: stock-check block-prepare
	RULES=$(RULES) CAP=$(CAP) ZESU_MAX_COQC=40 $(GUARD_BATCH) worker-build-2-block -- $(PYTHON) tools/block/blockrun.py \
	  --build-dir $(BLOCK_BUILD_DIR) --jobs $(BLOCK_JOBS) \
	  --cfg $(BLOCK_CFG) --function $(BLOCK_FUNCTION) --entries $(BLOCK_ENTRIES) --proof-dir $(BLOCK_PROOF_DIR) --trace-import $(BLOCK_TRACE_IMPORT) \
	  $(if $(STATES),--states $(STATES),) $(if $(LEADERS),--leaders $(LEADERS),) \
	  $(if $(BLOCK_OUTPUT_DIR),--output-dir $(BLOCK_OUTPUT_DIR),) $(if $(BASELINE),--compare $(BASELINE),) $(if $(IMPORT_MODULE),--import-module $(IMPORT_MODULE),)

# The segment table and the residual classes, from the records on disk.
.PHONY: report
report:
	$(PYTHON) tools/det/report.py

# What the guard has to say: memory, batch peak, kills.
.PHONY: guard-report
guard-report:
	@$(GUARD) report

.PHONY: check-local
check-local: check-evm-sail-snapshot check-evidence-tools
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

# Preserve selected instruction traces and check approved native region indexes.
STOCK_DECODE_TRACE_DIR ?= generated/isla-traces/stock-zisk/decodeItem
STOCK_CLOSURE_TRACE_DIR ?= generated/isla-traces/stock-zisk/closure
STOCK_TRACE_MANIFEST ?= build/stock-zisk/build-recipe.json
.PHONY: traces-closure-indexes
traces-closure-indexes:
	$(PYTHON) tools/stock_zisk/platform/traces.py --manifest $(STOCK_TRACE_MANIFEST) \
	  --dump build/stock-zisk/decodeItem.raw.dump --out $(STOCK_DECODE_TRACE_DIR) \
	  --coqdir ZesuSsz.Stock.DecodeItem --jobs 6
	$(PYTHON) tools/stock_zisk/platform/bind_traces.py --out $(STOCK_DECODE_TRACE_DIR) \
	  --check-manifest $(STOCK_TRACE_MANIFEST) --trace-name decodeItem
	$(PYTHON) tools/stock_zisk/platform/traces.py --closure --indexes \
	  --manifest $(STOCK_TRACE_MANIFEST) --out $(STOCK_CLOSURE_TRACE_DIR) \
	  --coqdir ZesuSsz.Stock.Closure --jobs 6
	$(PYTHON) tools/stock_zisk/platform/bind_traces.py --out $(STOCK_CLOSURE_TRACE_DIR) \
	  --check-manifest $(STOCK_TRACE_MANIFEST) --trace-name closure

# Restore tracked native index datasets before checkers or Dune start.
STOCK_NATIVE_TRACE_CACHE_DIR ?= $(CURDIR)/_build/stock-zisk/native-trace-cache
.PHONY: stock-native-indexes
stock-native-indexes:
	$(PYTHON) $(STOCK_TRACE_DRIVER) --ensure-native-indexes \
	  --manifest $(STOCK_TRACE_MANIFEST) --cache-dir $(STOCK_NATIVE_TRACE_CACHE_DIR) \
	  --decode-out $(STOCK_DECODE_TRACE_DIR) --closure-out $(STOCK_CLOSURE_TRACE_DIR) \
	  --dump $(DUMP) --jobs $(TRACE_JOBS)

check-evidence-tools check-signatures: stock-native-indexes
