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

An authorized PORT profile can request `"memory_booking": "full_physical_fence"`.
This option raises its booking to the unchanged 32 GiB fence.
It does not change the caller, authority, proof body, or CPU policy.
Profiles without this option keep their existing booking.
Blind PORT profiles reject this option and retain their separate policy.

A `focused_check` profile can also request `"memory_booking": "full_physical_fence"`.
It requires declaration-only execution and exact source coverage for every compiled module.
The booking equals the unchanged 64 GiB fence.
Focused profiles without this option keep their existing booking.
The unused empty native carrier does not receive a declaration workload.
The declaration-only executor does not run that carrier.

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
Historical input bytes live in `test-fixtures/historical-inputs`.
Tests materialize derived data in private temporary directories.
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

Authentic fixture bytes and origin hashes remain separate from derived data.
Derivation changes typed paths and dependent container hashes.
It preserves measurements, outcomes, and source bodies.
A missing historical object stays missing. Its compatibility check must refuse.
Fixture data never supplies admission evidence.

The digest cache checks device, inode, size, modification time, change time, and mode.
It checks the file identity before and after hashing.
Each operation resolves every bound path with a fresh parent map.
Startup and final acceptance force hashing of every retained input.
A provider publishes a private, hash-bound snapshot after its initial forced validation.
The snapshot retains every classified historical row.
It separately seals initial installed plugins and the selected compiler identity.
It binds the effective physical load paths.
Declaration jobs remove only declared output copies in their private workspace.
Donor objects and inherited bindings remain unchanged.
Snapshot publication requires those declared outputs to be absent.
A physical compile checks every retained file identity after guard admission.
It directly hashes its source, compiler, and complete load-path dependency superset.
Seed-reference runtimes retain full validation when snapshot coverage is incomplete.
The runtime stores its large binding inventory in a separate hash-bound file.
No historical row is removed.

Later dependency objects need receipts from successful, validated compilations.
Each private receipt binds its source, object, compiler, flags, job, and provider.
An authenticated index binds those receipt hashes to the initial snapshot.
Each index version remains immutable.
The authentication key never enters runtime files, receipts, logs, or the physical compiler environment.
Authentication does not replace file identity checks or direct hashing.
The compiler refuses a new dependency without an original binding or validated receipt.
Physical validation records its own costs separately from compiler costs.
The provider records validation time separately from each MCP call.
A provider session reuses validation while its runtime identity stays exact.
The session always runs full validation at completion, including after a tool failure.
Unchanged-runtime input mutations remain detectable at that final validation.

The persistent digest cache uses private storage and serializes each full identity key.
Forced hashing bypasses both digest caches.
Supplier validation reuses successful results only within one process.
Each hit checks all consulted file and namespace identities.
The monitor validates its fixed job policy before polling.
Each poll still checks aggregate identity, physical fences, and resource counters.

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


Controller exit cleanup follows the existing stock guard route.
Scratch supervisors track their child controllers through pidfds and exact PID start ticks.
Entry controllers track their stock batches with the same checks.
TERM, INT, HUP, Python failures, and normal exits close registered children.
The guard cleanup trap stops only its owned aggregate.
A failed child registration remains unknown and blocks claim release.
Cancellation before aggregate identity publication also retains an unproved claim.
Existing aggregate identity and actor closure checks remain authoritative.
Local cleanup handlers cannot cover SIGKILL or host failure.

The real cleanup control uses synthetic processes and real private cgroups.
It preserves a simultaneous foreign aggregate.
Run it explicitly with `python -m unittest tools.block.harness.controller_cleanup_real_control`.
It creates no Rocq process, PET process, compiler, or production claim.
Normal unit discovery excludes this control because it needs the host user service.

## Shared memory ledger

Canonical jobs and shell compiler reservations use the canonical `LEDGER.json`.
Both routes take `GATE_MUTEX` before `LEDGER.lock`.
Shell helpers reuse the authenticated inherited mutex descriptor.
They do not unlock the shell's descriptor.

The ledger retains each token and its owner.
The memory calculation groups only authenticated aggregate identities.
It charges the largest approved booking once per aggregate.
It charges verified current usage when that usage exceeds the booking.
Unknown or conflicting identities retain separate full costs.
Compiler slot counts remain separate.
Growth updates use the same transaction and preserve the token file identity.
The 175 GiB slice fence, 20 GiB headroom, and account limits remain unchanged.

A token release requires its exact generation, file identity, and closed compiler leaf.
Released token paths cannot serve another reservation.
The ledger retains the largest aggregate booking until authenticated aggregate closure.
A missing or replaced scope cannot silently release that booking.

A rollout needs a reviewed inventory of every old writer.
`prepare_legacy_rollout` builds a source-only seed without changing a live ledger.
Old aggregates retain their full authenticated fences until closure.
An old writer that can create an unrepresented aggregate blocks the rollout.
Older gate worktrees also need the unified writer before their next launch.
A managed tools checkout alone does not update an older Makefile or controller.
Do not migrate live records or change running jobs without rollout approval.
