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
The checker validates each source hash and each declared binder name, type, and order.
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
