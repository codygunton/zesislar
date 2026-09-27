# T6 diagnostic packet

Source branch tip: `55251ed462dba84daec0f92a87c8729a7d224e29`.
The diagnostic candidate was its ancestor
`5b19de9408b1bbad9b44a11e5d9c9046656467ac`.
The original review files identify each draft source and compiled environment.
The collection manifest in `det/nonraising-final/dd2b56436635` records
all copied hashes and source paths.

The diagnostic `.v.txt` files retain their original bytes. They are text
artifacts. They are not executable proofs. They include open goals and
`Abort`; no segment closure is claimed.
Support facts remain explicit diagnostic imports. They are not default imports.
The review files record times, residuals, and limitations.
Completed switched benchmark arms will be added separately.

## Diagnostic replay

The historical measurement used inlined T6 source over the `ed945cd357ac`
compiled environment. The packet does not contain that complete transient
load-path setup. It preserves the original diagnostic source and residuals.
Do not treat a later replay against the rebased candidate as that historical
measurement. A focused replay uses the matching compiled candidate snapshot:

```sh
rtk proxy tools/resource_guard.sh scope t6-replay -- tools/coqc_scratch.sh <private-diagnostic.v> <matching-arm-build-directory>
```

Copy the selected `.v.txt` file to a private `.v` path first. Keep each
support import explicit. Re-run only under root's queue authorization.
The future switched-arm JSONs will supply the exact preview candidate SHA
and import list. The packet currently makes no post-rebase measurement claim.

## 14f98Raw timing issue

`WriteSuccessTransactionsCarrierChunk14f98Raw.v` imports `AllLegacy`.
It does not import the T6 switch. The endpoint worker reports these traces:

| Source | CPU seconds | Elapsed seconds | Peak KiB |
|---|---:|---:|---:|
| `dd2b56436635` | 495.037367 | 498.601606 | 3870948 |
| `ed945cd357ac` | 274.220202 | 275.462971 | 3996012 |

At that checkpoint, the bounded low-load isolation was prepared but unrun.
These records do not establish a cause.
The current T6 source audit checks all 2508 tracked entries.
Every entry matches `55251ed462dba84daec0f92a87c8729a7d224e29`.
The root relayed this audit from the endpoint worker.

## Pre-probe failures

The T6 phase failed before probes. `Proofs/Tests/ReturnBundle.v`, line 9,
characters 10–22, reported this error:

```text
Cannot infer ?T in partial instance '?T -> Type' found for type islaG
```

The endpoint worker fixes this test. No T6 arm result exists.
The isolation preflight passed with zero `coqc` processes and load1 0.73.
The isolation command then failed before compilation because
`/usr/bin/time` was missing. The worker corrects the ignored command.
No isolation measurement exists. Integration remains `dd2b56436635`.
T6 is not merged.

## Completed low-load isolation

The bounded carrier isolation then passed with exit 0.
Elapsed time was 141.847 seconds. User CPU was 139.967 seconds.
System CPU was 0.400 seconds. Peak RSS was 3880308 KiB.
The scratch record reports 139673 ms.
The three tactic times are 32.694, 0.582, and 0.676 seconds.
No repair is required under the low-load isolation rule.
`isolation-14f98` preserves the exact source, command, and logs.
Its manifest verifies every copied byte hash.

The one-import test fix is pushed at
`6127efd7972be8dcde3871e9b6cd7bde4e96985d`.
The fresh snapshot verified all 2508 tracked entries.
Its 24-job preview runs as session 61346. No result is recorded yet.
No `.arm-commit` was created before this preview.
The sibling `6127efd7972b` directory preserves the snapshot audit.
The failed `55251ed462db` history remains unchanged.
