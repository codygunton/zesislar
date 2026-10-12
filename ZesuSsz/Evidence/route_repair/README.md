The acceptance command requires nine actual native closure certificates and two S119 rejection certificates.
The command also requires two linked loop negative applications.

```sh
python ZesuSsz/Evidence/check_decode_item_route_repair.py --results <ON-proof-bundle.json>
```

Use `--workspace <candidate-worktree>` when the owned proof sessions used another worktree.
The checker binds that workspace to the input seal, sources, calls, and closure records.
A certificate can bind an immutable `interactive_source` for MCP startup.
That file must contain the same declaration and complete pre-proof prefix as `proof_source`.
Its proof body must be empty and end with `Abort.`
Both sources must appear in the input seal.
Interactive exports must name `interactive_source`.
Final compilation, object attribution, and verification must name `proof_source`.
The array-store class uses the same command with `--array-store`.

Dry mode checks the retained captures and an uncompiled switch source:

```sh
python ZesuSsz/Evidence/check_decode_item_route_repair.py \
  --workspace <candidate-worktree> --dry-run \
  --switch-source <stub-directory>/ResourceFirstIntroduction.v
python ZesuSsz/Evidence/check_decode_item_route_repair.py \
  --workspace <candidate-worktree> --array-store --dry-run \
  --switch-source <stub-directory>/ArrayStoreSelection.v
```

Both commands report `accepted: false` and the missing certificates.
The stub checks only the module filename and reserved identifiers.
It supplies no typing, activation, or native closure evidence.
Use `--results <ON-proof-bundle.json>` in dry mode to check a complete linked bundle.
The checker applies every actual acceptance requirement to a complete bundle.
An incomplete bundle supplies no checked native certificate.
Remove `--dry-run` for acceptance when the complete evidence exists.
Real acceptance rejects a `--switch-source` override.
Dry mode rejects `--entry-normalization`.

Complete exports can include `kernel_groups` and `local_definition_export`.
The checker reads closure from the four ordinary groups.
It checks the kernel group counts, goal identities, contexts, and definition bodies separately.
A hidden or truncated kernel body rejects the export.

The reserved switch does not exist at this checkpoint. `DecodeItemRouteRepairSwitchIdentity` names the interface without activating it. The checked Rocq module states the nine complete native obligations. It supplies no proof of those obligations.

The bundle contains these fields:

- `repair_identity`: the exact `module`, `class`, and `instance` from `INDEX.json`.
- `verification_root`: the commit used for the actual ON proofs.
- `switch_source`: a file reference for the implemented production switch.
- `input_index`: a file reference for the immutable input seal. The seal contains `root` and an `inputs` map of absolute paths to SHA256 hashes.
- `native_cases`: nine records in the index order. Each record contains `block`, `proof_source`, `compiled_object`, `raw_calls`, `actual_final`, and `owned_closures`.
- `rejections`: two records in the index order. Each record contains `theorem` and `raw_calls`.

A file reference contains `path` and `sha256`. `raw_calls` contains the saved tool calls with `tool`, `arguments`, and `raw_response`. `actual_final` is the complete `rocq_complete_goals` response. Its export must contain all four actual groups with no remaining obligations. The native calls must show health, the exact theorem start, actual switch resolution, an advancing `zesu_block` request, Qed, compilation, and exact empty-assumption verification. The checker reports the actual verification methods.

The native source must preserve the captured declaration environment and exact theorem statement. The only permitted environment addition is the reserved switch import. The checker also binds the compiled object and normal owned cleanup. A pure certificate cannot satisfy a native case.

The S119 calls must verify the exact wrong-commitment rejection statements. They prove necessary-condition incompatibility. They do not prove that a retained native context is inconsistent.

`--check-inventory` checks the capture and statement hashes. It does not accept the repair. The three I75 terminal captures do not identify a precommitment assignment. The two I67 block-form captures have unavailable auxiliary groups. The four older precommitment captures retain their separate historical scopes. An actual ON proof must supply complete current groups for every site.

The same checker also binds the private `EntryNormalization` identity.
Use `--entry-normalization --check-inventory` to check its nine retained sites.
`ENTRY_NORMALIZATION.json` preserves the original statements, controls, and loop provenance.
The binding substitutes only the explicit switch import.
The proposed helper runs `zesu_integer_array_facts; simplify_eq` before the existing block dispatcher.
The source proposal did not run.
The checker requires the same linked certificates before acceptance.
Missing implementation or native certificates cannot establish acceptance.

The loop controls bind the committed cursor at `i` to the certified successor fact at `i+1`.
Each control records an exact failed S131 application and unchanged actual rollback groups `1/0/0/0`.
These controls are not False proofs or closed certificates.
Their frozen f203 scope and S131 verification scope remain separate from the candidate native scope.
Copy `loop_negative_controls` from `LOOP-NEGATIVE-RESULTS.json` into the completed ON bundle.
The checker validates raw calls, exact source and target hashes, scope, verified successor facts, and normal closure.
The nine native closures and both S119 certificates remain mandatory.
