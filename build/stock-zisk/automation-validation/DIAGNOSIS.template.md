# Rule diagnosis

Copy this file to `<item>/DIAGNOSIS.md`.
Keep this template unchanged.
Use one reviewed `TRACE.json` bundle for the complete diagnosis.
The checker uses the additive `terminal-verdict013` schema.

| Row | Evidence | Trace citations |
|---|---|---|
| trigger_goal | TODO | TODO |
| cycle.1.refusal | TODO | TODO |
| cycle.1.reason | TODO | TODO |
| cycle.1.normalization | TODO | TODO |
| cycle.1.next_refusal | TODO | TODO |
| terminal | TODO | TODO |
| candidate | TODO | TODO |

1. Quote the exact trigger goal from `goal` or `goal_nonotation`.
2. Quote the exposed clause and its refusal message in each refusal row.
3. Quote the observed reason from the same refusal state.
4. Quote each accepted normalization command in execution order.
5. Cite the next refusal, or quote `accepted` from the next rule command.
6. Repeat all four cycle rows for each further refusal.
7. Set `terminal` to `success` and cite the top-level verdict.
8. Form the candidate from the ordered sum of all normalization rows.

Use consecutive cycle numbers, starting at one.
Keep every cycle before `terminal` and `candidate`.
Write the candidate as `cycle.1.normalization + cycle.2.normalization`, with every cycle included.
Its citations must list the exact normalization commands in the same order.
Escape a Markdown table pipe as `\|`.

Every filled row needs a resolving local citation.
Use `relative/path/TRACE.json#/RFC6901/pointer`.
Resolve relative paths from the directory that contains `DIAGNOSIS.md`.
A path can name a reviewed trace in a sibling worktree.
Absolute local paths also resolve.
The checker reads JSON without executing cited content.

- Escape a key's slash as `~1` and its tilde as `~0`.
- Use zero-based array indices without leading zeros.
- Use percent escapes for URI-fragment characters when necessary.
- Put each citation in separate backticks.

Use backticks or JSON double quotes for exact observed strings.
Do not add inferred prose to the evidence cells.
A refusal row quotes both the exposed clause and the exact message.
It cites `/points/N/refusal/M/message` or `/residual/refusal/M/message`.
The refusal record must link to the refused rule trial through `hand_call_index`.
A reason cites the exact hypothesis, evar, log, goal, or refusal observation.
That observation must belong to the refusal's recorded before-state.
A normalization cites each `hand_call/M/commands/K/command` field.
The next accepted rule cites its `commands/K/outcome` field.
A repeated cycle must start at the preceding cycle's exact next refusal.

The checker requires one stable `session.id` across points and command snapshots.
Each command's `before` and `after` pointers must resolve inside `snapshots`.
The snapshots must preserve every public goal group and the complete evar map.
The next rule trial must follow the normalization chain without a state change.
The next trial must call the same rule.
Hidden focus frames are optional because the public observer cannot expose them.

A complete trace can have an unresolved verdict.
Such a trace is valid evidence but cannot complete this diagnosis.
An accepted rule call can mean progress only.
A completed diagnosis requires `actual-success`, whole-proof scope, and accepted `Qed.` evidence.
Its evidence pointer must be `#/completion/closure_check`.
The closure record must report no unresolved evars.
The final rule snapshot must contain no current, shelved, or given-up goals.
The trace must report proof closure and no residual.

The schema reserves `established-unsatisfiable` but defines no verified certificate payload.
The checker rejects `terminal = unsatisfiable` until that certificate contract exists.
A tactic refusal cannot establish unsatisfiability.
Review must still check whether the quoted observations explain the failure.
The checker validates provenance and state links, not the mathematical explanation.

Check the unfilled template:

```sh
python3 tools/block/check_diagnosis.py --template build/stock-zisk/automation-validation/DIAGNOSIS.template.md
```

Check a completed diagnosis:

```sh
python3 tools/block/check_diagnosis.py path/to/DIAGNOSIS.md
```

Template mode permits paired evidence and citation placeholders.
It still resolves every supplied citation.
Completed mode rejects placeholders and checks semantic evidence links.
Use `--structure-only` for preparation that cannot establish completion.
A template or structure-only pass never approves a candidate.
