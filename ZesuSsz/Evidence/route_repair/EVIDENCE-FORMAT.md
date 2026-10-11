# Linked route-repair evidence, version 2

The checker validates evidence consistency. It does not authenticate a transcript or execute a proof.
The exact nine native statements and two S119 controls remain fixed by INDEX.json.
Historical unavailable groups cannot establish acceptance.

The bundle contains `version: 2`, the existing repair identity, `verification_root`,
`candidate_delta`, `switch_source`, `input_index`, `sessions`, `native_cases`, and `rejections`.
`candidate_delta` records `base_root` and hash-bound `source_overlays` separately.
The base root is the frozen comparison root. The verification root identifies the candidate artifacts.

Every file reference contains `path` and `sha256`.
Each session contains `id`, `workspace`, `verification_root`, `owner`, `raw_calls`, and `closure`.
The owner contains its server `pid` and `start_ticks`.
Every referenced call contains `session_id`, `controller_owner`, `tool`, `arguments`,
`request_UTC`, `elapsed_seconds`, and `raw_response`.
An optional parsed `result` must equal the raw result.
Session labels, owner annotations, timings, workspace, and root are controller provenance.
They are not MCP session attestations.
Preserve unsuccessful calls and unavailable states in the bound transcript.

Each closure contains `session_id`, the same `owner`, `transport_closed_normally`,
`server_exit_verified`, `cleanup_signals_sent`, and `termination_fallback_calls`.
Both counts must be explicit zero integers.
The closure identifies an owned `pet` with `pid` and `start_ticks`, plus `Pet_exit_verified`.
A standalone session can instead record `pet: null` and `standalone_Pet_absent: true`.
Every used session needs a normal closure.

Each native case contains `block`, `proof_source`, `compiled_object`, `proof_trace`,
`compilation`, and `verification`.
Each rejection contains `theorem` and the same evidence fields except `block`.
A proof trace contains `session_id`, `health_call`, `start_call`, `steps`, `exports`, `export_attributions`, and `qed_call`.
Native traces also contain `activation_calls` and `native_operation_call`.
Every call reference is its zero-based position in that session's bound transcript.
State IDs are scoped to that session.

`activation_calls` maps the exact class Check and instance Print commands to call positions.
Each query records the controller's `context_state_id`.
Explicit tool state arguments must match that context.
The initial complete export follows the start and activation queries.
Every advancing rocq_check request has a preceding and subsequent complete export.
Its from-state must match the preceding export and raw advancing response.
Each subsequent export must match the new state.
The production raw response supplies the path, hash, bytes, state, and counters.
It does not supply theorem, source, workspace, or actual-group annotations.
The checker never adds these fields to the raw response.
Each export attribution contains `method: controller_complete_export`, `session_id`, `call`, and `state_id`.
It also contains `workspace`, `theorem`, the exact `source` reference, and the `export` reference.
The checker links this controller attribution to the start and advancing state chain.
All four groups must be arrays. A stack frame contains two arrays.
Counters and byte counts must match the bound export file.
The final export must contain four empty arrays before Qed.
Qed must reference that exact final state and report proof_finished.

The native operation reference names a measured rocq_check request whose entire body is
`zesu_block.` or `try zesu_block.`. A substring or comment does not suffice.
The checker requires a positive commands_run result.
This observation does not expose internal search branches or establish performance equivalence.

Compilation records contain `session_id`, `health_call`, `call`, and `object_attribution`.
The referenced compile request must name the exact source and workspace.
Compilation must use full mode, which is also the tool default.
A declaration-only vos pass cannot certify a retained vo object.
The attribution file contains `method: controller_post_compile_hash`, `session_id`, `call`,
`workspace`, the exact `source` reference, `object` reference, and `input_index` reference.
The retained .vo hash belongs to this controller attribution.
A successful raw MCP compile response alone does not attest the output object's bytes.

Verification records contain `session_id`, `health_call`, and `call`.
The raw request must contain the exact proof source, theorem name, workspace, and indexed declaration.
The raw result must report module_m or shared_defs with assumptions [].
Compilation and verification can use separate owned sessions.

The input index contains `root`, `workspace`, `inputs`, `roles`, and `modules`.
`inputs` maps absolute resolved paths to SHA256 hashes.
The required roles are `hooks`, `finish`, `approved`, `hints`, `plugins`, `mapping`, `findlib`, and `recipe`.
The plugin role contains a nonempty list of bound artifact references.
All other roles contain one bound file reference.
Unchanged local sources must match the frozen base root's Git blobs.
Changed local sources must occur in the explicit, hash-bound source overlays.
This includes changes to Hooks, Finish, Approved, and DecodeItemHints.
The checker rejects an omitted local source change.
The checker resolves overlay paths before duplicate and provenance checks.
Producers can retain original paths in separate controller records.
Untracked generated sources use overlays with `kind: frozen_generated_input`.
These overlays identify frozen inputs, not semantic changes.
Other overlays can use `kind: semantic_change`, which is the default.
Generated overlays require `candidate_delta.frozen_generation` with `manifest` and `source_index` file references.
The original generation manifest and frozen source index must occur in the sealed inputs.
External library sources retain their hash-bound artifact closure.
Every proof source, candidate overlay, role, module source, and module object must occur in inputs.
`modules` maps each logical import to its source and compiled object references.
The checker follows Require imports transitively, including From imports and nested comments.
An unrelated seal containing only the switch cannot pass.
The collector must bind the actual runtime mapping, findlib record, plugin artifacts, and recipe.
Hash coverage alone does not attest that an omitted runtime dependency was loaded.
