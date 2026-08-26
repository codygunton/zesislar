# Zesu contract viewer

This viewer comes from `binary-regions-speedscope@03685e14`.
It contains the Zesu speedscope fork, its profile converter, and its payload checks.

The repository does not store `node_modules`, `dist`, or generated profiles.
Run `make check-viewer` after `npm ci` in `ZesuSsz/Viewer/speedscope`.
Nix adds the generated Level 1 evidence payload to the built viewer.

The viewer keeps the complete advanced interface from that worktree.
ZesuSsz changes only the input status data and build integration.
Contract status is review data and is not a Rocq assumption.
