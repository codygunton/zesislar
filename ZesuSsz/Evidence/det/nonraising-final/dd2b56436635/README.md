# Confirmed non-raising evidence

Source commit: `dd2b5643663568543a21a5a2ebc72fcf853725b0`.
Raw corpus baseline: `434db04166fad748449e9d3104b05844f372a59e`.
Isolated baseline: `ed945cd357acd5d0b4e8a5030eb89264428ae6a8`.

The collection manifest records each exact copied file and its SHA-256.
Raw benchmark JSONs remain under `Evidence/residuals/benchmark`.
Analytical reconciliation remains separate in this directory.
The reconciled views replace only the 26 matched keys with isolated rows.
They do not replace the raw benchmark records.

Raw totals change from 216 to 328 closures and 450 to 73 errors.
The reconciled totals change from 218 to 328 closures and 456 to 73 errors.
All reconciled Iris outcomes match by key.
Pure adds 102 closures and removes 375 errors.
Unfold adds eight closures and removes eight errors.
No closed result is lost.

Root ran 26 matched isolated pairs at one compiler per pair.
Every pair has an identical outcome and goal hash.
The diagnostic script text is retained as `.py.txt` evidence.
The matched capture sources are retained as 52 `.v.txt` fixtures.
The queue log and all raw goal records are retained.
No diagnostic text is installed as tooling or executable proof source.

## Reproduction

Run the corpus arm from integration with the current determinism runner:

```sh
rtk proxy /home/cody/zesislar/.worktrees/determinism/tools/resource_guard.sh batch nr-corpus -- python3 /home/cody/zesislar/.worktrees/determinism/tools/residual/benchmark.py --automation dd2b5643663568543a21a5a2ebc72fcf853725b0 --set /home/cody/zesislar/.worktrees/determinism/ZesuSsz/Evidence/residuals/corpus_all_set.txt --name corpus --jobs 32 --no-reprobe
```

The fixed set SHA-256 is
`95c00989213e01cf438f35f687104687197f59ac3c45721af0ea88bdecf64372`.
The population map SHA-256 is
`505ab2bc63ee951d67d4aaf4fe3d2c74a6a35d93684e20999ccb7f5156b18415`.
The selected statement audit found no changed or missing statements.

The isolated script uses `benchmark.capture` with each existing compiled
arm and the current guarded scratch tool. It alternates the baseline and
candidate for each key in `iris-reprobe-set.txt`. Each call uses the standard
variant and a 300-second limit. It stores the complete goal and error record.

Root's first full preview failed on `WriteSuccessExactStorageKeysStores.v`
with an allocation failure. Both isolated full proofs passed at
12.285 and 12.536 seconds, with approximately 1.4 GiB peak memory.
The full preview retry passed in 42.296 seconds. Root then merged this commit.
The precise initial allocation cause remains unresolved.

The two completed v2 baseline arms use the explicit `Sets.v2` import and
standard re-probe policy. Their exact raw files are included. The T6, T3, and final standard records are included in their separate directories.
All four final arms have zero delta against their specified baselines.

## Verification archive

The verification directory retains the v1 fast checks and both full previews.
It includes the failed allocation record and both passing isolated store checks.
It also retains the focused test sources and logs.
The verification manifest records every copied file hash and source path.
All copies preserve the original bytes.
The 52 matched fixtures are text evidence, not executable proof modules.
No build artifact is included.
