# Rebased T3 evidence

Candidate SHA: `f08fa35bf956c933c951580727194ffcb0932334`.
The candidate rebases onto `6127efd7972be8dcde3871e9b6cd7bde4e96985d`.
The candidate and original backup branches are pushed.

Root reviewed all 23 files. Twenty-two match the original candidate exactly.
`Finish.v` adds only the T3 import and selector to the 6127 source.
It preserves the non-raising v1 entry. `prearm-status.json` records this review.

Check-fast passed at 24 jobs in 346.28 seconds.
Its peak was 63 GiB. It reported zero timeouts.
The log manifest verifies both exact fast logs.

`t3-phase-commands.json` records both exact switched arm commands.
Each enables `Sets.v2` and `Switches.ArrayLoadPriority` explicitly.
Root's arm session 93339 builds the immutable snapshot at requested 32 jobs.
No arm result or T3 merge is claimed at this checkpoint.

The T3 writer also audited the immutable candidate snapshot.
All 2530 tracked blobs and Git modes match the candidate SHA.
There are zero blob, mode, or missing-entry mismatches.
There are no non-blob entries. `writer-source-audit.json` attributes this
read-only audit to the T3 writer through root. Build and probes remain pending.

## Failed arm build

The f08 arm build failed before probes. `Proofs/Tests/ArrayLoadPriority.v`,
line 5, characters 7–20, reported `Cannot find module ListNotations.`
No benchmark result exists. `preprobe-failure.json` preserves the exact error.
`t3-rebased-arms.log` preserves the raw build failure.
The T3 writer fixes the import and compiles the exact test file.
An inlined rule header does not verify that file's imports.
