# Native launch preflight

Designed native discovery requires `--entry-artifacts`.
The JSON map contains these fields:

- `schema`: the integer `2`.
- `function`: the exact design function name.
- `objects`: a map from Rocq module names to object bindings.
- `lookup`: the selected-code and instruction-map bindings.

Each object binding contains an absolute `path`, a SHA256 `sha256`, and an integer `bytes` count.
Bind every direct `Require` module in the rendered sources.
Include external dependency objects with their exact installed paths.
The checker validates their hashes and actual loaded paths.

The `lookup` object contains these fields:

- `selected_code`: the exact qualified selected-code name.
- `index_module`: the exact qualified map name, with the suffix `.instr_map`.
- `index_source`: the generated index source, with its exact file binding.

Discovery renders every pending selected declaration before creating the worker pool.
The declaration stage opens an `Abort` view in an owned MCP session.
It checks health, entry elaboration, loaded objects, complete exports, and owned closure.
The resource stage uses a separate diagnostic with the same source prefix.
It requires the selected-code `LithiumUnfold` instance and opens that code through existing tactics.
It checks `liFindInContext` at the literal entry PC.
It requires the function's own lookup map.
It discharges the membership condition and checks the exact selected instruction.
The diagnostic executes no machine instruction.
The original primary statements and bodies stay unchanged.

Every selected entry must pass both stages before any new native worker starts.
Each worker checks the retained receipts, sources, objects, index source, and checker code again.
A refused entry prevents the launch.
A declaration-only pass cannot release a worker.

Admission evidence stays separate from the legacy result report:

- `entry-preflight-sources/` contains the exact full rendered sources.
- `entry-preflight/declarations/` contains the separate declaration receipts.
- `entry-preflight/resources/` contains the separate resource receipts.
- `entry-preflight/REPORT.json` binds both complete stages.
- `entry-preflight/POLICY.json` binds the artifact map, resources, objects, and checker code.

The checker saves every raw SDK response before parsing.
A refused entry remains readable even if later fallback handling fails.
An absent design class uses the report-only label `unclassified-design-entry`.
Existing class values remain unchanged.
The abstract-stop diagnostic path keeps its existing behavior.

## Artifact caller controllers

Future artifact controllers must use the shared two-stage CLI before requesting a primary operation:

```sh
"$ZESU_MCP_PYTHON" -B tools/block/launch_preflight.py \
  --manifest launch-manifest.json \
  --output /owned/workspace/_build/fresh-launch-preflight \
  --mcp-command /owned/workspace/tools/rocq_mcp_guarded.sh
```

The manifest contains `schema`, `workspace`, `function`, and `rows`.
The schema is the integer `1`.
Each row contains `entry` and `resource`.
Each `entry` contains `id`, `source`, `theorem`, and `artifacts`.
The source uses the same exact file binding fields.
The artifacts map binds exactly the direct `Require` modules for that entry.
Each `resource` contains `pc`, `selected_code`, `index_module`, and `index_source`.
The PC is a hexadecimal literal that matches the original `instr_body` declaration.
The output must be fresh and inside the workspace.

The controller must require exit status zero and `passed=true` for every selected entry.
The controller must bind the combined receipt and both stage receipts in its launch packet.
The controller must bind the exact original sources, objects, resource fields, and checker code.
The controller must reject changed inputs before its primary call.
A different source or artifact requires a fresh preflight.
The guarded launcher and compiler admission remain active.
The factory selects the complete-goal exporter and the current MCP Python explicitly.
Preserve the `tools/` directory structure when copying the external checker.

The separate `launch_entries.py` CLI checks declarations only.
The separate `launch_resources.py` CLI requires a passed declaration receipt.
Their manifests remain separate for diagnostic controls.
Artifact controllers must use the combined CLI for launch admission.
A preflight pass establishes resource lookup only.
It does not establish instruction progress or native proof closure.
