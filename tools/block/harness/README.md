# Shared block harness

Use this directory for new block runs.
Keep historical private harnesses unchanged.

Pin one complete Git commit with `--harness-commit`.
The harness refuses a different checkout or an uncommitted implementation.
The runtime records the commit and the harness tree in `HARNESS.json`.
The cache collector still checks actual proof inputs and execution vectors.
Git identity does not replace proof, object, statement, or dependency checks.

Supply an explicit target adapter and an exact base runtime.
The adapter binds all targets, generated sources, and import edges.
The planner checks their complete dependency closure.
The planner never compiles other native proof bodies as setup.

```sh
python -B tools/block/harness/scratch.py BLOCK ENTRIES.v \
  --harness-commit COMMIT \
  --base-runtime RUNTIME.json --base-runtime-sha256 DIGEST \
  --target-adapter ADAPTER.json \
  --normalization-policy POLICY.json \
  --output OWNED_OUTPUT --prepare-only
```

The command creates a managed detached checkout for its launch commit.
Preparation and execution use that checkout.
Later changes to the base HEAD do not change an active launch.
Do not edit a managed launch checkout.
`--run` uses the commit bound in its runtime.
Use `--harness-commit NEW_COMMIT` with `--refresh-memory` to select a newer harness.
The refresh preserves the prepared proof inputs and records the prior harness.
Use an all-exit watcher for execution.
Keep source and input identities exact when an object is reused.

Setup and compilation have no CPU stop.
Native search retains its selected policy.
The memory fence and the shared parent remain unchanged.
Unmeasured probes book their full fence.
Measured families book their validated claim and observed growth.

Before an external stop, the harness retains the complete available export.
An in-flight tactic has no returned internal state.
The report labels a pre-call export explicitly.
Current internal counts remain unknown in that case.

Run static transport audits through the commit-time tests.
New launches retain typed projection and complete prospective input checks.
They do not repeat the static source audit.

Each supplier must provide an activation control.
That control must execute the new rule through the actual public entry point.
A declaration import alone does not establish activation.
Keep its exact statement and its accepted `module_m` result with empty assumptions.
Retain the previous supplier's refusal when that evidence exists.

Interactive evidence that uses `abstract` requires physical confirmation.
Compile the unchanged file.
Require successful `module_m` checks with empty assumptions after importing its object.
Inline compiler prints do not replace these checks.

The migrated `test_*.py` files preserve the existing regression controls.
Some historical controls require their original bound development artifacts.
The portable tests in `tools/test_shared_harness.py` require no proof artifacts.

The repository test suite runs portable controls in a separate process.
The Makefile runs the migrated suite through `MCP_PYTHON`.
That interpreter must provide the installed `mcp` and `rocq_mcp` packages.
Override `MCP_PYTHON` when that interpreter uses a different path.
Run the migrated regression suite with the installed MCP interpreter:

```sh
tools/resource_guard.sh batch block-harness-controls -- \
  /home/cody/.local/share/uv/tools/rocq-mcp/bin/python -B -m unittest discover \
  -s tools/block/harness -p 'test_*.py'
```

Historical positive controls require their original retained development inputs.
A missing historical object stays missing. Its compatibility check must refuse.
Synthetic unit data never supplies admission evidence.

The digest cache checks device, inode, size, modification time, change time, and mode.
It checks the file identity before and after hashing.
Each operation resolves every bound path with a fresh parent map.
Startup, physical compilation, verification, and final acceptance force full hashing.
The provider records validation time separately from each MCP call.

The observed outer gaps are consistent with two measured validations.
They are not measurements of prover time.
Direct operation timings must confirm any remaining overhead.

Every shared CLI command enters `zesuworkloads.slice` before preparation.
The parent retains its 175 GiB fence and zero swap.
Imported preparation and execution operations also require that parent.
An environment flag cannot replace the actual cgroup check.

Stock gates use reviewed family measurements only for the exact command and fence.
An unmatched command retains the full fallback claim.
The recorded cache provenance stays unknown for the retained PR54 measurements.
These measurements support admission predictions, not cold-build performance claims.
The physical gate fences remain unchanged.

A supplier release requires explicit verification success.
`module_m` and an empty assumption list cannot replace that success flag.
