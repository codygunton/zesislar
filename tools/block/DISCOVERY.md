# Designed-entry discovery

The discovery driver runs existing entry declarations independently.
It does not infer a new entry from an incoming edge.
It records descriptive entries as specification gaps.
It does not change a contract or prove a complete contract.

The driver reads the block design, CFG, manifest, and executable entry data.
The entry data names an existing resource predicate and its source hash.
The driver checks block extents, successor sets, source hashes, and the selected artifact identity.
Each executable block receives abstract successor continuations.
Return blocks use an explicit symbolic return expression.

Run this command from the worktree under the pinned opam switch:

```sh
opam exec --switch=/home/cody/islaris -- \
  /home/cody/.local/share/uv/tools/rocq-mcp/bin/python tools/block/discovery.py \
  --design ZesuSsz/Evidence/decode_item_block_design.json \
  --entries build/stock-zisk/designed-entry-discovery/entries.json \
  --cfg build/stock-zisk/cfg.json \
  --manifest build/stock-zisk/build-recipe.json \
  --out build/stock-zisk/designed-entry-discovery \
  --terminal 'decodeItemReturnAddress args' --jobs 6 --seconds 300
```

Each worker starts an isolated, guarded Rocq MCP server.
The driver calls `rocq_health`, `rocq_start`, and `rocq_check`.
Every start loads a separate source whose proof contains only `Proof.` and `Abort.`.
The full source remains separate for explicit proof requests and final compilation.
The report binds both sources. Document loading cannot run the generated block tactic.
The existing chain renderer supplies each diagnostic source.
The existing recorder retains active goals and shelved goals separately.
The server uses a 6-GiB memory limit without swap.
Each probe has a 300-second limit across its MCP calls.

The report preserves each block's first residual and exact outcome classes.
The instruction-lookup class uses the generic `FindInstrKind` goal head.
An absent PC marker remains an unknown residual location.
A setup error does not count as a proof residual.
A reached abstract continuation does not establish its contract.

`--resume-report` reuses successful diagnostics only when the complete generated source hash remains equal.
The driver also checks the previous contract, design, CFG, and manifest hashes.
It records reuse explicitly.
The initial monitor can count Pet twice in older captures.
Those captures retain a conservative RSS bound and the independent MCP peak measurement.
The current monitor counts each process once.

The supplied entry data references seven existing resource sites.
The other seventeen designed entries require executable declarations from the specification owner.
The diagnostic sources use the existing predicates without adding register values or memory resources.

The driver also reads executable entries directly from the design JSON.
Omit `--entries` for this mode.
Supply `--trace-import` and `--code-premises` as explicit probe inputs.
The code-premise file contains the existing Rocq premise lines.
These options do not change the design schema.

The adapter consumes exactly these five contract fields:

- `entry_definition` contains a fully qualified Rocq Definition name.
- `binders` contains an ordered list of objects with `name` and `type`.
- `arguments` contains an ordered list of Rocq expression strings.
- `resource_predicate` contains a fully qualified Rocq Definition name.
- `source_hashes` maps repository-relative paths to SHA-256 hex strings.

The adapter retains the supplied argument order and expressions.
The existing renderer receives the resource predicate with those arguments.
The adapter adds the existing Iris context binders without assigning local values.
The report binds the five fields and every supplied source file.
Both Definition names must identify hashed source files.
A missing field, invalid shape, missing Definition, or changed source hash produces a specification gap.
The driver does not execute that entry.
A description without these fields remains a specification gap.
The legacy entry mode preserves the accepted seven-probe report.
The adapter does not rerun that report.

`--probe-import` adds an explicit module import to every design-schema probe.
Use repeated options for the approved automation switches and required type imports.
The report binds each local module source and records the import list.
These options add no contract resources.

`tools/block/archive_discovery.py` preserves complete capture bytes in a content-hash archive.
Its report utility keeps exact first conclusions and hashes the complete goals.
The timeout utility separates a failed entry query from a failed tactic transaction.
The last valid goal after a tactic timeout does not show execution progress.
A reached abstract successor remains a diagnostic result.

Design-schema discovery requires `--binding-report` from `tools/block/check_entry_bindings.py`.
The checker validates each source hash and each declared parameter type and argument arity.
JSON binders declare application-local variables.
The kernel checks the ordered arguments against the Definition parameter types.
It checks argument arity and compiles the unchanged ordered applications through Rocq MCP.
The JSON expression order remains authoritative.
Same-type swaps require specification review.
The consumer rejects failed checks, changed sources, and changed ordered applications.
The legacy entry mode retains its existing interface for frozen comparisons.

`tools/block/trace_registers.py` extracts footprints from manifest-bound native trace files.
It emits design and CFG fragments without changing either source file.
`regs_read` and `regs_written` include PC and all explicit native register events.
`regs_assumed` contains names referenced through Assume without an explicit event in that block.
The native frontend removes internal nextPC events from the raw Isla traces.
The exporter does not infer register liveness from disassembly fields.

The primary pass runs the unchanged `zesu_block` proof body.
Each primary transaction records elapsed time and the reported goal size.
A secondary pass runs only after a primary Coq tactic timeout.
That pass uses existing initialization tactics and individual `zesu_liAStep` commands.
Each diagnostic step records elapsed time, goal size, and the last successful state.
The secondary pass never determines the primary outcome class.

A failed 60-second `rocq_start` triggers the approved `coqc_scratch.sh` LOAD fallback.
LOAD compiles the exact source prefix through `Proof.`, followed by `Abort.`.
LOAD executes no block tactic and supplies no interactive Pet state.
A successful LOAD therefore records `primary-unavailable`, unless a separate ruling permits a fresh start.
The report distinguishes abstract successor captures from contract closure.

`replay_secondary.py` selects only hash-bound primary timeout captures.
Its secondary command uses `1: zesu_liAStep.` because the default selector requires one focused goal.
This command changes no primary source or primary outcome class.
The public MCP response truncates long goal text and returns only shelved counts.
The secondary fixed-point check compares active text and can miss changed shelves.

`--complete-goals` starts an owned MCP server with the reviewed read-only exporter.
The exporter saves active goals, stack entries, shelved goals, and given-up goals for each successful state.
Each session uses a separate output directory because state identifiers restart.
Export records bind the state identifier, full bytes, and hash.
The server executes no proof command during export.

`retry_loaded_entries.py` selects the three hash-bound unavailable entries.
It permits one fresh owned Pet start after each successful shell LOAD.
It verifies the unchanged source hash before that start.
A failed fresh start leaves the primary unavailable.
The runner executes no secondary pass and claims no contract closure.

`compare_ram_fault.py` compares 38 off/on pairs on one announced root.
Both arms use the same domain, code premises, abstract successors, and frozen primary bodies.
The off arm removes only the RamFault imports.
Kernel checks confirm the absence or presence of the switch instance before any primary probe.
The comparison measures the complete RamFault switch effect.
It does not isolate the Assert rule from other rules under that switch.
Historical results remain separate because their root and domain differ.
Each primary call records its exact arguments and timeout.
Secondary diagnostics remain disabled during this controlled comparison.
Each arm reports setup failures separately from native proof outcomes.

`tools/block/replay_secondary.py` reads the immutable primary report and archive index.
It selects only the recorded primary Coq timeouts.
It verifies each frozen source and primary capture before the diagnostic replay.
The secondary command is `1: zesu_liAStep.`.
The selector focuses the first active goal and retains every returned goal.
The replay adds no primary execution, outcome classification, or contract closure.
Its fixed-point check still compares returned active goal text only.
All returned shelved goals remain in the raw captures.
