# Restart candidate: isolated clone

The exact candidate `506fe57b84d20559aa87e52ef56843c2f2ca1af7` passed fetch and both gates.
The fresh clone used a detached checkout of that commit.
The clone remained tracked-clean.
Its manifest hash remained `ed8196f2d359dc1a60827a9ccb0267247e8b27f97f2d09763315af159c662e99`.
Its artifact identity remained `bd8f29b23700dca4ae8238585241b02143b3406a4c75a77aad78945f99947c37`.

| Gate | Elapsed seconds | Workers | Peak child RSS, KiB |
| --- | ---: | ---: | ---: |
| check-fast | 1085.838 | 2 | 2204684 |
| check-iris | 2502.519 | 2 | 983952 |

The sandbox hid other home projects and exposed only the declared host directories and the clone.
The EVM-Sail reference checkout remained a pinned, read-only host input.
The runtime used writable `/tmp`, `/dev`, and `/run/user/1000/zesu-guard`.
A separate syscall audit checked 9325 artifacts and 79 inputs.
It found no undeclared paths under `/home`.
The syscall audit covers manifest verification only.
The full gates ran without syscall tracing.

`target-prod-restart-isolated.json` records commands, source revisions, measurements, allowed paths, and archived log hashes.
The coordinator owns tag creation and publication.
The cross-host runtime retrieval and complete toolchain lock remain documented gaps.
