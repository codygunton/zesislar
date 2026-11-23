# Agent-assisted proofs: `txAccessList` and its array-list callees

## Context

The block-automation plan (issue #316) ended with `decodeItem`, `nextUint64` and `decodeParentHeader` proved (132 blocks).
Its held-out runs showed what stops new code: the generator's inference and missing contract facts, not the rule library (3 of 255 unseen blocks closed).
This plan stops growing that inference. Every point where the generator stops becomes a typed request; agents propose the answer and the Rocq kernel checks it; cheap models prove the narrow goals.
It proves `rlp_decode.txAccessList` and its three array-list callees (130 blocks, 4 functions) with that pipeline, proves agreement with Sail's `decode_access_list`, and then sizes `rlp_decode.decodeTxFields` (591 blocks), the last unproved RLP decoder.

Terms used below:

- **Obligation**: one thing the kernel must accept: a block, a leftover goal of a block, a pure lemma of the Sail agreement, or a decision.
- **Leftover goal**: a goal that `zesu_block2` leaves open. It is *pure* (a proposition) or *spatial* (an Iris entailment).
- **Request**: a typed question raised by a generator stop or refusal.
- **Annotation**: the checked answer to a request: an assertion at a program point, or the placement of a memory access.
- **Decision**: a request whose answer must be invented: a contract, a loop assertion, a callee premise. Its *floor* for a function is 1 contract + 1 assertion per loop cut + 1 premise per unproved callee.
- **Tier**: one model setting used as a prover, ordered by cost.
- **Run directory**: `_build/agents/aa/<function>/`, outside the source tree.

All measures in this plan are counts of tasks, obligations, decisions, attempts, lines, bytes and tokens. No time or CPU measure decides anything.

## Approach

Work runs in lanes: one worktree per lane under `.worktrees/aa-<lane>` on branch `aa/<lane>`, pull requests through the existing gates, a new tracking issue referenced by every pull request. Read the current tree from `origin/main` (`084364765` or later); the main checkout is 1,253 commits behind.

### Stage A: tooling (tasks A0–A9; A0 first, the rest independent unless stated)

**A0. Cleanup before any run.** `_build/BUDGET.json` (measured 2026-11-22) shows 270 GB of unique build data against the 200 GB total budget and agent `rebuild` at 84 GB against its 80 GB budget; the resource guard refuses runs over budget, and `/home` is 90% full. Do these in order and record the counts before and after.

1. Stop stale processes of the finished plan: list with `tools/bg list --active`, stop each watcher and bank keeper with `tools/bg stop <id>`.
2. Copy the Unicorn harness `_build/agents/researcher/exec-check/harness.py` and `drive.py` to `tools/oblig/exec/` in the first tools lane (A3 item 7 rewrites them); they exist nowhere else.
3. In `_build/agents/rebuild/` and `_build/agents/heldout-render/` (48.7 GB and 24.4 GB of large JSON not shared between runs), write `SEALED.json` in every run dir, with `KEEP.json` in `rebuild/heldout2` listing `census-all.json`, `census.tsv`, `TRACES-READY`, `ho2-traces.log`. Small text files (notes, `STATE.md`, `leftover/Goal*.v`) survive a shrink without a keep entry.
4. Remove worktrees that lose nothing: for each of the 415 worktrees, when `git status --porcelain` is empty, its head is reachable from a local branch or `origin/main`, and `tools/build_janitor.py in-use <path>` exits non-zero, run `tools/cleanup_after_merge.sh <branch>` if the branch is merged into `origin/main` (it moves saved goals and closure records to `_build/goals/` and `_build/closures/` first), otherwise move its saved goals with `tools/goal_store.py` (`rescue`; exact call: unverified — confirm first) and run `git worktree remove <path>` without `--force`. Branches stay. 195 worktrees are `heldout*` and 42 are `bench*`. Write every dirty worktree to `_build/janitor/worktrees-dirty-<date>.tsv` and leave it.
5. `make janitor`, read its plan, then `make janitor-apply`. Done when `_build/BUDGET.json` shows `total_over` false.
6. Bring the main checkout to `origin/main` with `git pull --rebase` (it holds one local commit and is 1,253 commits behind). If an untracked file blocks the checkout, move it to `_build/agents/aa/carry/` first. Delete one of the two identical untracked copies `TXACCESSLIST_PROOFS_PLAN.md` and `TX_ACCESS_LIST_PROOF_PLAN.md`, and move the other to `docs/AGENT_ASSISTED_RLP_PLAN.md` if it equals this plan.
7. Delete each local branch that `git merge-base --is-ancestor <branch> origin/main` accepts and no worktree has checked out (944 of 2,029 today), with `git branch -d`; leave any that `-d` refuses. Remote branches are not touched.

**A1. Close-out and rules.** Three pull requests.

1. Set `BASELINE` in `tools/soundness_gate.py:22` to the `origin/main` head. The description holds the full diff, from `0140e6874` to that head, of every file in `PUBLIC` and `PUBLIC_CONTEXTS` (`tools/block/check_function_closure.py:8-19`).
2. Commit `docs/BLOCK_AUTOMATION_REBUILD_PLAN.md`, `docs/GENERATOR_FIRST_PRINCIPLES_REPORT.md` (both untracked in the main checkout) and this plan as `docs/AGENT_ASSISTED_RLP_PLAN.md`. Open the tracking issue. Open a second issue, "Relocatable proofs", with the text given in A9.
3. Amend `AGENTS.md`:
   - *Proof pattern*, sentence "Report the residual goal to the lead and fix the rule in `Automation/`." becomes: "File the residual goal in the obligation store (`tools/oblig/store.py`). The router decides between a checked lemma, an annotation and a rule."
   - *Integration gates*, sentence "Auto adds a generic rule only when one manual step needs more than five lines or at least two proof sites need the same step." becomes: "Add a generic rule only when the store shows one goal class open in two functions, or in five goals of one function, and one stated rule closes all of them. Close every other goal with a checked lemma in `ZesuSsz/Residuals/`."
   - *Proof workflow* step 5 becomes: "File every residual goal and every generator stop as an obligation. Agents propose annotations and proofs. Only the kernel accepts them."
   - Sentence "Treat rapid proof-size growth as an automation defect, not as routine proof work." becomes: "Report checked-lemma lines and tokens per block for every function. Growth per block from one function to the next is the defect signal."
   - New section *Generator freeze*: "Do not add inference to `tools/block`. Two kinds of change are allowed: a fix for a crash or a wrong output, and code that consumes an annotation and emits its check. Every stop and refusal becomes a typed request (`tools/oblig/derive.py`)."
   - New section *Agent provers*: "Agents are untrusted. Their text enters the tree only through a renderer that copies checked text byte for byte. The user reviews every statement in the trust base (function contracts, callee premises, known-bug classes, Sail agreement statements), and `ZesuSsz/Evidence/SignatureGates.v` pins it. Annotations inside a function need no review. Start each goal at the cheapest tier of `tools/oblig/routing.json`. Never send an unchanged prompt to the same tier twice."
   - *MCP discipline*, add: "The stand-alone lemma check of the obligation loop (`check.sh` under the resource guard) is an approved shell route."
   - New section *Relocatable artifacts*: "A hand-written or agent-written file names code and data by symbol and offset, never by absolute address. Absolute addresses appear only in generated files. `tools/oblig/check_relocatable.py` enforces this for the files it lists."

**A2. Obligation store** — new `tools/oblig/store.py`, model-free.

- Data: one append-only event log per function, `<run dir>/OBLIGATIONS.jsonl`, written under `flock`. `store.py status` folds it into the current state.
- Event row, schema `oblig-event/1`: `id`, `function`, `kind` (`block`, `goal`, `meaning`, `decision`), `parent`, `state`, `class`, `tier`, `attempt`, `prompt_sha256`, `prompt_bytes`, `answer_bytes`, `tokens_in`, `tokens_out`, `context_items`, `context_used`, `artifact` {`path`, `sha256`}, `head`.
- States: `derived`, `running`, `closed`, `failed` (with `class`), `false`, `waiting-decision`, `blocked-on` (with the blocking `id`).
- Ids: `<function>/block/<case>`, `<function>/goal/<case>-<first 16 hex of the statement sha256>`, `<function>/decision/<kind>-<offset>`, `<function>/meaning/<lemma name>`. `<case>` and `<offset>` are 4-hex offsets from the function's symbol.
- `store.py sync --function F --run RUN` derives states from existing evidence and adds no second source of truth: `CALLERS.json` rows, `CLOSURE.json` and `NOT-CLOSED.json` (`tools/closure_cert.py`), `goals/<id>/STATUS.json` (`tools/block/residual_loop.py`), `results.jsonl` (`tools/bench/bench.py`).
- The store rejects an attempt event whose (`prompt_sha256`, `tier`) pair already exists for that id.
- No model reads the log. A prover reads one task file, at most the tier's `max_prompt_bytes`. A decision agent reads one request package. The coordinator reads only `store.py status --counts` (one line per state and kind) and `route.py next --limit N` (one line per item). `report.py` prints the coordinator's bytes read per round.

**A3. Goal packaging** — new `tools/oblig/package.py`, wrapping `tools/block/residual_loop.py` (`export`, `collect`, `register`, `rerun`), which stays the engine for pure goals.

1. *Falsity check*, new `tools/oblig/falsify.py`. For a pure `goal.v` it builds `exists <binders>, <premises> /\ ~ <conclusion>` and tries a fixed list of at most 200 concrete assignments, each evaluated inside Rocq with `vm_compute`, so a hit is a kernel-checked counterexample. It runs no machine code and no symbolic search. Values: 0, 1, each literal of the statement and its neighbours, `2^k - 1` and `2^k` for k in 8, 16, 32, 64, the RAM bounds `0xa0000000` and `0xc0000000`, byte lists of length 0, 1, 55 and 56, and, for binders named after a machine register or a contract argument, the values of the machine-run snapshots of that block (item 7). A hit sets state `false` and attaches the assignment; the goal goes to the owner of the statement, never to a prover. A goal with a binder type outside `Z`, `nat`, `N`, `bv n`, `list byte` and `bool` is marked `unchecked`.
2. *Slicing.* Keep the reachable-premise slice of `ZesuSsz/Automation2/ResidualExport.v`. The task file shows the default-printer goal and gives the path of the exact source (the existing `TASK` text of `residual_loop.py`).
3. *Similar lemmas*, new `tools/oblig/similar.py`. Index every closed pure lemma (the 68 in `ZesuSsz/Residuals/Block800d*.v`, the 10 in `DecodeItemBridges.v`, every goal closed later) by conclusion head and set of qualified names. A task gets the 3 nearest by Jaccard similarity, each with its proof, inside the tier's prompt limit.
4. *Spatial leftovers.* Today `zesu_diag_export_final` (`ZesuSsz/Automation2/Diagnostics.v:200-208`) prints `@@X skip final spatial`. Add `ZesuSsz/Automation2/SpatialExport.v` and its switch `SpatialExportOn.v`. With the switch on, that branch prints one `@@S` record: the head of the stuck judgment, the address or register it seeks, one line per owned resource of the context, and the pure facts that share a variable with the sought term. `package.py` adds the block's disassembly, its hint slice (A4) and the successor entry statements, and writes a *diagnosis task*. Its answer is typed, not a proof: `annotation` (a changed or added row for A6), `pure_goal` (an exact pure statement that unblocks the lookup; it becomes a new `goal` obligation), `false` (the entry statement is wrong, with a counterexample), or `rule_gap` (stated as a stand-alone entailment for the rule lane). The check is a rerun of the block.
5. *Answer form for provers*: JSON `{"verdict": "proved" | "false" | "need_context" | "give_up", "proof": "...", "needs": [...], "counterexample": "..."}`. `package.py` writes `answers/<id>.v` and `answers/<id>.json` for `residual_loop.py collect`.
6. *Module naming.* `tools/residuals/render_residual_module.py` and `residual_module_failures` in `ZesuSsz/Evidence/check_proof_hygiene.py` (about lines 606–621) accept only `Block800d<block>.v`. Add the form `ZesuSsz/Residuals/<Function>/Block<4 hex offset>.v` with lemma names `residual_<function>_<offset>_<16 hex>` for new functions. The 16 existing files stay. (`module_name` in the renderer: unverified — confirm first.)
7. *Machine runs*, new `tools/oblig/exec/run.py`, rewritten from the Unicorn harness that ran `decodeParentHeader` (Unicorn 2.1.4, RV64, pinned ELF; A0 item 2). `run.py --function F --inputs FILE --at <offset>,...` runs the function on each input and writes `<run dir>/exec/<input id>/STATE-<offset>.json` (all registers, and the memory ranges the contract owns) each time control reaches an offset. Hooks replace `memcpy` and the allocator entries `alloc`, `remap`, `resize`, `free` with a bump allocator; `--alloc-fail N` makes the N-th allocation return null. Inputs for `txAccessList`, in `tools/oblig/exec/inputs/txAccessList.json`: access lists with 0, 1 and 2 entries carrying 0, 1 and 3 keys, and five malformed ones (not a list, 19-byte address, 31-byte key, truncated entry, trailing byte). Inputs for the array-list regions: list states with length 0, 1 and capacity, at capacity and below. `annotations.py test` (A6) instantiates the binders of a proposed assertion from every snapshot at its offset and evaluates its facts with `vm_compute`; one failing snapshot rejects the proposal and returns the input id. Snapshots at a loop cut, one row per visit, also go into the decision package. Machine runs only filter proposals; no statement or proof cites them.

**A4. Hint pack** — new `tools/oblig/hints.py`. Hints are untrusted and never enter a statement unchecked.

- Input: the pre-link object named by `inputs.object` in `build/stock-zisk/build-recipe.json` (`tools/stock_zisk/fetch_inputs.py` fetches it), read with `get_dwarf_info(relocate_dwarf_sections=False)`. It holds 502 structure types, 1,640 members and 23,301 location entries; the linked ELF holds only a symbol table.
- Reuse `code_dwarf` and `inline_ranges` (`tools/stock_zisk/dwarf.py`) for relocation to linked addresses, and `die_attribute`, `die_source`, `die_ranges` (`tools/stock_zisk/inventory.py`). New code reads `DW_TAG_structure_type` and `DW_TAG_member` (offsets, sizes), `DW_TAG_formal_parameter` and `DW_TAG_variable` with `DW_AT_location` (register or frame slot per pc range), and the line table.
- Source text: `_build/p0c-zesu-source` at commit `b5483dda…` (`sources.zesu` in the recipe); `txAccessList` is `src/stateless/rlp_decode.zig:485-538`.
- Output in `<run dir>/hints/`: `SOURCE.md` (numbered source of the function and of each function inlined into it), `TYPES.json`, `LOCATIONS.json` (pc range → variable → register or frame slot), `BLOCKS.md` (per block: disassembly, source lines, inline stack, live registers, variables in scope).
- `hints.py slice --pcs ...` cuts the part for one request.

**A5. Tier replay and routing table** (needs A2, A3 items 1–3 and 5).

- Corpus: the 68 proved residual lemmas, with their proofs withheld (known true); the unique statements among the 786 `leftover/Goal*.v` files under `_build/agents/rebuild` and `_build/agents/bench` (truth unknown; they test the falsity check and the `false` and `give_up` verdicts).
- Tiers in `tools/oblig/tiers.json`, cheapest first:

  | Tier | Model selector | Use |
  |---|---|---|
  | `mechanical` | none (`CONTROL_TACTIC` of `tools/residuals/residual_package.py`) | every goal first |
  | `haiku-low` | `anthropic/claude-haiku-5-5:low` | default first model tier for pure goals |
  | `haiku-medium` | `anthropic/claude-haiku-5-5:medium` | second |
  | `haiku-high` | `anthropic/claude-haiku-5-5:high` | third |
  | `sonnet-medium` | Sonnet at medium (model id: unverified — take it from the configured model list) | only under the 50% rule below |
  | `opus-medium` | `anthropic/claude-opus-5-5:medium` | last prover tier; all decisions and diagnoses |

  Each tier has `max_attempts` 2 and `max_prompt_bytes` 12,000 at the start.
- Model selection per call: remove the line `perCallModel: "off"` from `.omp/config.yml`, and set `task.perCallModel: eval` and `task.perCallModelAllow` (the selectors of the table) in the user config `~/.omp/agent/config.yml`; a project config cannot turn this setting on. Then re-read `xd://eval/agents` for the parameter that carries the selector.
- Each proved lemma goes to every tier independently, with the lemma renamed and no repository path in the prompt, so each tier's success rate is measured on the same goals.
- Kernel-side driver `tools/oblig/dispatch_kernel.py` (loaded with `%load` in the coordinator's eval kernel) maps a tier to `agent(...)` or `completion(...)`, writes the answer files and records prompt bytes, answer bytes and tokens. The tools under `tools/oblig/` call no model.
- Output: `tools/oblig/routing.json`: for each goal class (the ids of `tools/bench/triage_classes.json`, with `PURE` split by conclusion head into linear arithmetic, bitvector, byte window and meaning predicate) the first tier, the attempts per tier and the context recipe (premise slice only; plus similar lemmas; plus hint slice).
- If the three Haiku tiers together close under 50% of the 68, add `sonnet-medium` to `perCallModelAllow` and replay it; otherwise the tier stays out of `routing.json`.

**A6. Derivation, requests, annotations** — new `tools/oblig/derive.py` and `tools/oblig/annotations.py`.

1. `derive.py --function F --run RUN` runs `tools/block/render_function.sh` and writes `<run dir>/derived/`:
   - `LIVE.json`, from `liveness` in `forward/FORWARD.json`;
   - `FRAME.json`: every stack slot read or written, with its size and first writer;
   - `JOIN-STATEMENTS.json`: for each join outside a loop cut, the exact disjunction of its incoming states, from `forward/JOINS.json`;
   - `CALLEES.json`: each call of `build/stock-zisk/cfg.json` with the callee's row in `ZesuSsz/Contracts/proved_functions.json` (`proved`, `assumed`, or none);
   - `CONTRACT-SKELETON.v`: argument registers, pointer ranges and structure layouts from the hint pack, with the meaning left open. It is input for the contract decision, not a statement.
   - `REQUESTS.json`: one row for each `stops` entry of `FORWARD.json`, each `refused_*` row of `render/RESULT.json`, each refusal in `forward/LOOP-DESIGNS.json`, and each `CallRefused` message.
2. Request row: `id`, `kind`, `pc`, `reason` (the generator's own reason string), `needs`, `derivable`, `proposal`. Kinds: `contract`, `callee_premise`, `loop_assertion`, `join_assertion`, `access_placement`, `call_row`, `predicate`. `derivable` is true when the derived files fix the answer (an exact join statement; an access at base plus a constant); then `derive.py` fills `proposal`, and the proposal is checked like any agent answer.
3. Annotation file `tools/block/functions/<F>.annotations.json`, schema `zesu.annotations.v1`. Row: `id`, `request`, `at` {`pc` (written `+0xOFFSET` from the function's symbol, or `SYMBOL+0xOFFSET`, the form `resolve_symbol_keys` in `tools/block/function_profiles.py` reads), `boundary`: `entry` | `loop_cut` | `join` | `call_site` | `call_return` | `function_return` | `access`}, `binders`, `resources`, `facts` [{`coq`, `role`}], `placement` {`array`, `index`, `scale`, `offset`}, `author` {`tier`}.
4. `annotations.py compile` writes the function profile `tools/block/functions/<F>.json` with the existing keys (`loop_heads`, `loop_designs`, `join_designs`, `calls` with `return_facts`, `hist_visible`, `frame_slots`) and a key `generated_from`. `annotations.py check` fails when the profile differs from the compiled annotations. The three existing profiles stay hand-written.
5. Annotation consumption in the generator, the only generator feature work: a `placement` row resolves an access that the forward pass stops on (reason `unsupported` or `state_check` in `tools/block/forward_design.py`) to the named array at the given index, and emits `0 <= index < length` as a pure check. A `call_row` may name the length expression of a returned array, the case `tools/block/call_boundary.py` refuses at about line 606. (Exact hook points in `forward_design.py` and `symbolic_state.py`: unverified — confirm first.)
6. Bug fixes, after confirming each on `origin/main`: the `common_root_ancestor` crash and the uncaught `BoundaryRefused` in `tools/block/render_fp301_entries.py` (about lines 392–405 and 676–687) become refusal rows; a stop inside a seeded join reaches the join's boundary.
7. *Rounds.* Generation resumes by itself: a stop ends only its path up to the next cut (loop head, join, call return), and after an answer `annotations.py compile` and `derive.py` run again with no model. `derive.py` writes each round to `<run dir>/round-<n>/`, because `render_function.sh` skips a step whose output exists. Round 1 issues, before any forward pass, every request that the control-flow graph alone fixes: the contract, one `loop_assertion` per cut, one `callee_premise` per callee without a row in `proved_functions.json`, one `call_row` per call. Only `access_placement`, `join_assertion` and `predicate` requests may appear in later rounds. A block reruns only when its caller text or an imported generated module changed (compare `caller_sha256` of its `CLOSURE.json`).

**A7. Router and report** — new `tools/oblig/route.py` and `tools/oblig/report.py` (needs A2).

`route.py next --function F --limit N` prints work items by these rules:

| State of the obligation | Next step |
|---|---|
| block `derived`, or an input changed (annotation, lemma) | rerun the block; no model |
| proposed assertion or contract | `annotations.py test` on the machine-run snapshots; no model |
| pure goal, not yet checked for falsity | `falsify.py`; no model |
| pure goal `false`, or `rule_gap` | owner of the statement (decision queue), with the counterexample |
| pure goal that names a code address | class `ADDRESS`, to the decision queue (A9) |
| pure goal, falsity check passed | `mechanical`, then the first model tier of its class in `routing.json` (`haiku-low` unless the replay moved it) |
| attempt failed with a compiler error | same tier once more with the error text, then the next tier (`haiku-medium`, `haiku-high`, `opus-medium`) |
| verdict `need_context` | add the named item when the hint pack or the similar-lemma index has it, same tier; counted as a missing-context failure |
| top tier failed | `waiting-decision`: the assertion that produced the goal is reconsidered |
| spatial leftover | diagnosis task at `opus-medium`; its typed answer creates the next obligation |
| decision request with `proposal` | check the proposal; no model |
| decision request without `proposal` | decision task at `opus-medium` with the request, the hint slice, the derived files and the annotations already checked |

An obligation with 6 attempts in total, or reset 3 times by a changed annotation, is marked `spin` and reported; it gets no further attempt until its statement changes.

`report.py --function F` prints: blocks closed with no model; rounds, and requests per round; decisions made against the floor; share of requests with `derivable` true; unhandled refusals; proposals rejected by machine runs; missing-context failures per attempt; share of supplied premises and similar lemmas absent from the accepted proof (from the premise minimiser of `residual_loop.py`); goals found false after a model attempt; prompt bytes and tokens per attempt; coordinator bytes read per round; per tier, the share closed at the first attempt and within its attempts; share closed by Haiku tiers; escalations; tokens per closed obligation per tier; spin count; tokens and checked-lemma lines per block.

**A8. Sail transaction modules and scope note.**

- Add `generated/evm-sail-coq/transactions/dune`, modelled on `generated/evm-sail-coq/rlp/dune`, with modules `evm_decode_access_list_tx_types` and `evm_decode_access_list_tx` only. Today no build stanza or Rocq file imports that folder.
- Add `runDecodeAccessList` to `ZesuSsz/Compliance/SailRun.v` beside `runParentHeaderFields` (line 125). (`runDecoder` is declared `Local` at line 106 yet other files unfold it: confirm before reuse.)
- Write `docs/PROOF_SCOPE.md` from `_build/agents/rebuild/heldout2/census-all.json`: counts of functions with indirect jumps (125), with loops (98), calling functions without a contract (203); `memset` and other platform instructions; termination; recompilation; the largest functions.

**A9. Relocatable artifacts, the minimum.** The aim: when a function moves, repair is regeneration and a mechanical rerun. Only what follows is in this plan.

- Already relative, keep using: profiles keyed by symbol and offset (`resolve_symbol_keys`), 4-hex offset case names, residual statements (no code address in `ZesuSsz/Residuals/` today).
- New `tools/oblig/render_symbols.py` writes `ZesuSsz/Generated/Stock/Symbols.v` from the `.symtab` of `build/stock-zisk/zesu-zisk.elf`: one parsing-only `Notation` per symbol listed in `tools/oblig/symbols.json`, its body the address literal. New contracts and premises name an entry, a callee or a data address only through these notations.
- New `tools/oblig/check_relocatable.py`, run by `make check-fast`: it fails on a match of `0x800[0-9a-f]{5}`, `2148[0-9]{6}` or `21474[0-9]{5}` in the files listed in `tools/oblig/relocatable_files.json`. The list starts with every non-generated file this plan adds (contracts, premises, candidates, compliance, residual modules, annotation files). `package.py` applies the same patterns to each exported `goal.v`.
- Not done here, recorded in the "Relocatable proofs" issue: the roughly 1,175 absolute-address matches in 47 files of the three proved functions (some pinned by signature gates); generated lemma names `DesignedBoundary_<pc>` (`tools/block/render_function_callers.py:231`) and traces named by address; a relink drill (shifted layout, regenerate, rerun, expect zero model tokens); and the note that a symbolic base address inside Rocq would need new Islaris instruction maps and pc arithmetic.

### Stage B: prove-out, leaf first (tasks B0–B6)

Targets, from `build/stock-zisk/cfg.json`:

| Region name | Symbol | Entry | Blocks |
|---|---|---|---|
| `keysToOwnedSlice` | `array_list.Aligned([32]u8,null).toOwnedSlice` | `0x800d677c` | 27 |
| `entriesToOwnedSlice` | `array_list.Aligned(input.AccessListEntry,null).toOwnedSlice` | `0x800d6554` | 27 |
| `keysEnsureCapacity` | `array_list.Aligned([32]u8,null).ensureTotalCapacity` | `0x800cb40c` | 23 |
| `txAccessList` | `rlp_decode.txAccessList` | `0x80000000` | 53 |

`txAccessList` has 323 instructions, a 576-byte frame, and one cyclic region with backward edges to `0x800000c4`, `0x8000018c` and `0x800002ec`. Its 12 calls: `decodeItem` at `+0x64`, `+0xd4`, `+0x108`, `+0x158`, `+0x19c`; `keysEnsureCapacity` at `+0x1f4`; `keysToOwnedSlice` at `+0x258`; `alt_fl_alloc.remap` (`0x8004218c`) at `+0x33c`, `alt_fl_alloc.alloc` (`0x80042494`) at `+0x3d0` and `alt_fl_alloc.free` (`0x80041f38`) at `+0x428`, each a `jalr` through a pointer loaded from the allocator's function table; `memcpy` (`0x800e06c0`) at `+0x3fc`; `entriesToOwnedSlice` at `+0x49c`.

**B0. Inputs.** For the four regions: Isla traces in the closure group (`generated/isla-traces/stock-zisk/closure`, index modules `ZesuSsz.Stock.Closure.index_<region>`), and `ZesuSsz/Contracts/<Region>Selected.v` in the form of `NextUint64Selected.v`. (Trace command: unverified — confirm first from `_build/agents/rebuild/heldout2/TRACES-READY` and `ho2-traces.log`.) Build the hint packs (A4) and run `derive.py` (A6) on all four.

**B1. Statements (decision tasks; the user reviews the result).** One review packet, `<run dir>/STATEMENTS.md`, holding:

- A contract per region in `ZesuSsz/Contracts/<Region>Contract.v`, stated with `IslarisContractResources` and `IslarisContractCorrect`. Every pointer that is read through lies in RAM (`0xa0000000` up to `0xc0000000`); every pointer and length has a numeric range; each contract has an instance that exposes ranges and links as plain facts, in the style of `ZesuSsz/Automation2/DomainRanges.v`.
- Allocator premises in `ZesuSsz/Contracts/AltFlAllocPremises.v`: `altFlAllocCallPremise`, `altFlRemapCallPremise`, `altFlFreeCallPremise`, plus one for `resize` if an array-list region calls it. Each has the form of `memcpyCallPremise` (`□ instr_pre <pc> <call spec>`, `ZesuSsz/Contracts/ParentHeaderMemcpyService.v`). The `free` premise reuses `freeEntryResources` and `freeExitRegisterResources` of `ZesuSsz/Contracts/AltFlFreeContract.v`. Each gets a row with status `assumed` in `proved_functions.json`.
- The function table: the entry resources own the table cells that hold the allocator addresses (slots 0, 8, 16, 24: `alloc`, `resize`, `remap`, `free`, per `ZesuSsz/Evidence/generate_zesu_cfg.py:393-395`) and return them unchanged, so each `jalr` target is a loaded word with a known value.
- The reference decoder `ZesuSsz/Contracts/Candidates/AccessListCandidate.v`, modelled on `Candidates/ParentHeaderCandidate.v`, following `rlp_decode.zig:485-538`. The outcome relation has an out-of-memory outcome beside result and `error.InvalidBlock`, since `alloc` may return null.
- The Sail statement: `TxAccessListMeaningModuloKnownBugs` = domain ∧ candidate result ∧ (Sail agrees ∨ a registered bug trigger), the shape of `ParentHeaderMeaningModuloKnownBugs`. Sail's `decode_access_list` (`evm_decode_access_list_tx.v:982`) returns `AccessListRef` with an encoded slice, an address count and a slot count, and fails above `2^30` bytes. "Sail agrees" therefore means: Sail accepts exactly when the candidate accepts, and on acceptance the address count is the number of entries, the slot count is the total number of keys, and the encoded slice is the consumed input.

While the review is open, B2–B5 proceed on the proposed statements. A statement the review changes resets the obligations under it.

**B2–B4. Regions in order: `keysToOwnedSlice`, `entriesToOwnedSlice`, `keysEnsureCapacity`.** For each: answer its requests (A6, A7), render, run every block with no model (`tools/bench/mkset.py`, then `tools/bench/bench.py run --dump-leftover`), package the leftovers (A3), route them (A7), register checked lemmas, and rerun until every block has a `CLOSURE.json`. Then compose the region theorem `<region>Compliance`, add its `proved` row and interface to `proved_functions.json`, and render `ZesuSsz/Compliance/<Region>BlockObligations.v` with `tools/block/render_open_blocks.py`. `entriesToOwnedSlice` is the same source function as `keysToOwnedSlice` at another element size; its decisions, tokens and lemma lines against the first measure reuse.

**B5. `txAccessList`.** Same loop. The five `decodeItem` calls use `ZesuSsz.Interfaces.DecodeItem` and call-slice instances in `ZesuSsz/Contracts/TxAccessListCallSlice.v`, modelled on `ParentHeaderCallSlice.v`. The three array-list calls use the interfaces from B2–B4. Cut assertions are needed at `+0xc4`, `+0x18c` and `+0x2ec`; the annotation compiler lists them in `loop_heads` with hand rows in `loop_designs`, which override inferred designs. Result: `Theorem txAccessListCompliance : TxAccessListContractCorrect` in `ZesuSsz/Compliance/TxAccessListCompliance.v`, with code `txAccessListSelectedCode ∗` the three array-list selected codes `∗ decodeItemSelectedCode ∗ memcpyCallPremise ∗` the allocator premises.

**B6. Sail agreement** (parallel with B2–B5; needs A8 and B1). Statement first: an `opus-medium` decision task writes the lemma list from the candidate decoder down to `_rec_decode_access_list_entries` (`:936`) and `_rec_decode_access_list_keys` (`:889`), as goal directories. Each lemma is a `meaning` obligation routed like a pure goal. `render_residual_module.py --shared` renders the checked lemmas into `ZesuSsz/Compliance/TxAccessListSailAgreement.v`. Each divergence found becomes a proposed `KnownBug` constructor with its trigger in `ZesuSsz/Contracts/TxAccessListBugTriggers.v`; adding a constructor waits for the user's review. Pin the reviewed statements in `ZesuSsz/Evidence/SignatureGates.v`.

### Stage C: size the next function (task C1)

Run B0's derivation only (hint pack, `derive.py`) on `rlp_decode.decodeTxFields` (`0x8000050c`; 591 blocks, 2,825 instructions, 49 loops, 87 calls, one jump table). Record in the plan's status section: requests by kind, the decision floor, callees by status, the jump-table request, and the projected tokens from the per-block figures of Stage B. No proof runs.

### Targets

| Measure | Target |
|---|---|
| Blocks certified | 130 of 130; open-block records with 0 fields |
| Decisions per region | at most 2 × floor |
| Goals found false after a model attempt | 0; each one found adds its assignment to the falsity list |
| Pure goals closed by Haiku tiers | at least 70% |
| Goals that reach `opus-medium` as prover | at most 10% |
| Obligations left in `spin` | 0 |
| `entriesToOwnedSlice` against `keysToOwnedSlice` | at most half the tokens and half the new lemma lines |
| Generator lines added under `tools/block` | reported; only A6 items 5 and 6 |
| Rounds per region | at most 3 |
| Absolute addresses in new non-generated files | 0 (`check_relocatable.py`) |

A missed target is reported with its cause in the status section; it does not block the theorem.

## Critical files and anchors

- `tools/block/residual_loop.py` — `TASK` (462), `cmd_collect` (599), `minimize` (641): the pure-goal engine that A3 wraps.
- `ZesuSsz/Automation2/Diagnostics.v:200-208` — `zesu_diag_export_final`: where spatial leftovers are skipped today.
- `tools/block/render_function.sh` — the render steps; its outputs `forward/FORWARD.json` (`stops`, `liveness`) and `render/RESULT.json` (`refused_*` rows) feed `derive.py`.
- `ZesuSsz/Contracts/ParentHeaderMemcpyService.v` — `memcpyCallSpec2`, `memcpyCallPremise`: the form of every callee premise.
- `tools/stock_zisk/dwarf.py` — `code_dwarf`, `inline_ranges`: DWARF reading and relocation that A4 extends.

## Verification

- Tools: tests `tools/oblig/test_*.py` beside each new tool, run by the tool suite of `make check-fast`. They cover: a false statement is refuted by `falsify.py`; the store rejects a repeated (`prompt_sha256`, `tier`); `annotations.py compile` reproduces the `loop_designs` and `join_designs` of `tools/block/functions/nextUint64.json` from equivalent annotation rows; `derive.py` turns a recorded `refused_incomplete_boundary` row into a `join_assertion` request.
- Tools on old ground: `store.py sync` on `decodeParentHeader` reports 98 closed blocks and 0 open obligations.
- Machine runs: `tools/oblig/exec/run.py --function decodeParentHeader` reproduces the results recorded in `ZesuSsz/Evidence/PARENT_HEADER_EMULATION.json`; `annotations.py test` rejects a loop assertion with a deliberately wrong bound and names the input.
- Relocation: `check_relocatable.py` passes on the new files and fails on a fixture that contains `0x800d6960`.
- Cleanup (A0): `_build/BUDGET.json` shows `total_over` false; `git worktree list` holds no clean worktree outside the keep rule.
- Each pull request: tools only → static checks and `make check-fast`; `ZesuSsz/Automation2/` (A3 item 4) → the full cycle with `make check-iris`; contracts and compliance → static checks, `make check-iris`, `make check-fast`, and `make check-signatures` when a reviewed statement changes.
- Per region: `tools/closure_cert.py` certificate for every block; `tools/block/render_open_blocks.py --check` with 0 open fields; `tools/block/check_proved_functions.py`.
- Final: `Print Assumptions txAccessListCompliance` prints "Closed under the global context"; the same for the Sail agreement theorem; `rocq_verify` through rocq-mcp on both statements; `tools/soundness_gate.py` passes against the new baseline.
- New behaviour seen end to end: `report.py` for each region prints every measure of the targets table, and each closed goal's event log names the tier that closed it.

## Assumptions and contingencies

- **Allocator and `memcpy` stay premises.** The theorem lists them. If the user wants `alt_fl_alloc.free` proved (43 blocks, contract exists), it is one more region after B4.
- **Function table ownership.** If the table lies in memory the machine map cannot state as owned cells, the allocator premises state the three loaded words as facts instead; this changes B1's packet only.
- **Zig standard library source is not on this host** (the nix store path of the recipe is absent). The array-list regions then get hints from DWARF only. If a `zig-0.16.0` source tree is supplied, `hints.py` reads `lib/std/array_list.zig` from it and records its SHA-256.
- **Per-call models.** If `perCallModel: eval` cannot be enabled, map the tiers to agent names instead: `sonic` for `haiku-low`, `scout` with its override raised to `:high` for the other Haiku tiers, `task` for `opus-medium`.
- **Token counts.** If the harness exposes no per-agent token usage, the store records prompt bytes, answer bytes and the harness cost line, and the report prints bytes.
- **Three cut points in one cyclic region.** If `tools/block/loop_design.py` refuses a cut with more than one entry edge, accepting a hand row there is an annotation-consumption change under A6 item 5.
- **Sail agreement strength.** Sail returns counts and a slice, not decoded entries, so agreement on content beyond those is not statable against it. If the user wants a stronger statement, it needs a new Sail-side definition and is outside this plan's theorem.
- **Review timing.** If the user's review of B1 changes a contract after blocks closed, those blocks rerun; lemmas whose statements no longer occur are dropped from the residual modules by the renderer.
- **Cleanup scope.** A0 removes only clean worktrees and merged local branches and shrinks sealed run dirs. If the janitor still reports `total_over` after A0, list the ten largest remaining run dirs and ask the user before deleting any.
