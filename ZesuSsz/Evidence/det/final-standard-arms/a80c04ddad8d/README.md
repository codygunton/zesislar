# Final standard arms

Source SHA: `a80c04ddad8daa85e335fb26f21bc9d99c6c99f3`.

The v1 full arm has two closed rows, 302 residual rows, and one timeout.
The timeout was reprobed alone.
All four comparison fields match the `ed945` baseline.
The v1 rule15 arm has two closed rows, 45 residual rows, and one timeout.
Its timeout was reprobed alone.
All four rule15 comparison fields match the `ed945` baseline.
Both exact `ed945` v1 baseline files are included.
The v2 full arm has seven closed rows, 274 residual rows, and 24 errors.
All four fields match the `dd2` v2 baseline.
Its 25 re-probes include one batch timeout that resolved in isolation.
The v2 rule15 arm has six closed rows and 42 residual rows.
All four fields match the `dd2` v2 baseline.
It required no re-probe.
All four final arms completed.
The final Evidence check-fast passed at 24 jobs, with a 52 GiB batch peak.
It reported zero timeouts.
The exact Dune target took 17.316 seconds.
The driver timestamps bound the elapsed span to 42.053–43.053 seconds.
Root push is queued after the green gate.

These frozen Iris arms measure regressions.
The separate corpus analysis measures 102 pure closures and eight unfold closures gained.
The corpus gains do not imply closure gains in the frozen Iris arms.

The archive manifest records exact source paths and SHA-256 hashes.
Raw benchmark bytes remain unchanged.
The progress comparator is a snapshot after the first completed final arm.

The final manifest preserves all raw arm files, the comparator, and the queue log.
The retired `f08` source audit is historical.
That snapshot failed on the test import before probes.
The corrected `a80` snapshot supplied the completed T3 and final results.

Two prior attempts failed before compilation.
The first lacked the build parent directory.
The second lacked the generated trace links.
Root repaired these links and reran the unchanged gate controls.
All three driver logs and the passing proof log are included.
