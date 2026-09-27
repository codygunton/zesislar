# Fixed T3 source and stable build store

Source SHA: `a80c04ddad8daa85e335fb26f21bc9d99c6c99f3`.
Its only source change from `f08fa35bf956` is the test's two imports.
The fresh source audit verified all 2530 tracked blobs and Git modes.
Tracked source in both snapshots remains unchanged.

The new snapshot uses retired `f08fa35bf956/_build` as its physical store.
The ownership wrapper maps only this source root to that store's owner.
All other roots retain their original slot ownership.
The global cap remains 48. Fair share remains 32.
Gate and arm checks retain their 30-second interval.
The exclusive ownership record prohibits rebuilding or deleting f08.
The wrapper retains the original measurement and re-probe logic.

The 24-job full preview passed with zero timeouts and reported peak 45 GiB.
Its exact Dune proof target took 3.958 seconds. Production modules were not
recompiled. The driver timestamp span is between 55.172 and 56.172 seconds.
The timestamps do not supply an exact whole-command elapsed measurement.

Root then completed the proof and Automation targets against the physical
store. Root created the new arm marker only after these targets passed.
The retired f08 snapshot remains unmarked.
The archive manifest verifies the preview, completion, hygiene, provenance,
and physical build records.

The T3 switched arms run as session 50432. Their results remain pending here.
No T3 merge or Phase C completion is claimed by this packet.

## Measured full arm

The full 305-row switched arm completed with 7 closed, 274 residual, and
24 error results. All 24 errors were re-probed.
Outcome, class, signature, and goal hash match the dd2 v2 baseline by key.
All four delta counts are zero. Metadata and marker validation passed.
No closure was lost. No new error or timeout exists.
The raw arm, exact command manifest, and comparator result have verified hashes.
The rule-15 arm remains pending. No rule-15 result is inferred here.

## Measured rule-15 arm

The 48-row switched arm completed with 6 closed and 42 residual results.
It has no error or timeout. No re-probe was needed.
All four per-key fields match the dd2 v2 rule-15 baseline.
Metadata, frozen-set, and re-probe validation passed.
Both T3 arm deltas are zero. Neither arm loses a closure.
The post-arm full preview is running. Its result remains pending.
All four final standard arms also remain pending.

## Reviewed post-arm merge

The post-arm full gate passed at 24 jobs with zero timeouts and peak 44 GiB.
Its cached Dune proof target took 0.849 seconds.
The driver timestamp span is between 38.833 and 39.833 seconds.
Root then merged the exact a80 source. Earlier pending statuses are historical.

The writer worktree has no uncommitted tracked work.
The root archive preserves 33 ignored diagnostic files with verified hashes.
Its path and selected curated records appear in `writer-archive-record.json`.
Only generated/build symlinks remained untracked; they require no data archive.

All four final standard arms remain pending. Their session is 28859.
This packet claims neither CP3 completion nor Phase C completion.
