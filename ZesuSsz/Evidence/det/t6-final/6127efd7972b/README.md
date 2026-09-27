# Corrected T6 preview

Source SHA: `6127efd7972be8dcde3871e9b6cd7bde4e96985d`.
This commit fixes the test import. Its fresh snapshot audit verifies
all 2508 tracked entries. The earlier `55251ed462db` history remains separate.

The first snapshot preview failed before proof compilation. An uncached
tooling test could not create `_build/agents/push1` because its parent was
absent. That attempt took 8.201 seconds. The raw driver log remains preserved.

The corrected full preview passed at 24 jobs in 2369.61 seconds.
The reported peak was 111 GiB. The preview reported zero timeouts.
`preview-log-manifest.json` verifies all four exact copied logs.
`status.json` records the earlier running state; it is historical.
`preview-summary.json` records the completed result.

Root must complete the benchmark build before creating `.arm-commit`.
The ignored completion script uses the existing runner's `build(snapshot,24)`.
That call checks proof targets and `@ZesuSsz/Automation/all`.
It calls `mark_built` only after both targets pass.
This evidence worker did not run the completion script or create the marker.
The mandatory post-arm preview still follows the switched arms.

## Completed switched arms

The full T6 arm adds two closures and three errors.
The rule-15 arm adds one closure and two errors.
Neither arm loses a closure or adds a timeout.
The exact raw JSONs remain unchanged under `Evidence/residuals/benchmark`.
`t6-arm-deltas-final.json` preserves every per-key change and validation check.
`arm-command-manifest.json` preserves the exact commands and imports.

The endpoint worker captured all three new errors. Each reports:

```text
Expected a single focused goal but 0 goals are focused.
```

The integer probe stops at line 89, at `iSplit` in an earlier frame adapter.
The two optional probes stop at line 219, at `iSplit` in an earlier Some adapter.
None of the three target proofs starts. These are earlier probe-source errors.
The packet preserves stdout, stderr, exit metadata, source hashes, and
`.v.txt` fixtures. Each fixture hash matches its capture metadata.
This diagnosis does not alter or reclassify the raw arm outcomes.

Root's post-arm 24-job preview runs as session 43453.
Its result remains pending in this packet. T6 merge is not claimed here.

## Reviewed merge

The post-arm full preview passed in 39.358 seconds at 24 jobs.
Its peak was 43 GiB. It reported zero timeouts.
Root then fast-forwarded integration to
`6127efd7972be8dcde3871e9b6cd7bde4e96985d`.
Root removed the completed T6 writer worktree after this archive was verified.
Root remains unpushed until the final four arms. Both candidate branches are pushed.
The T3 worker rebases onto this root.

`postarm-log-manifest.json` verifies the exact gate, completion, and hygiene logs.
Hygiene freed 0.00 GiB and reports 542G available on `/home`.
The hygiene log reports 28 worktrees. Earlier pending statuses are historical.
