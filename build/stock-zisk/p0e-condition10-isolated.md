# Condition 10: isolated clone gates

Both gates passed in a fresh clone of `38e9e06e93e241683f05dd2664e9b6d1b79f089d`.
The clone fetched all three pinned source checkouts under `_build`.
The fetch command retained the manifest and artifact identity.
The clone had no tracked changes after both gates.
The worker and clone manifest hashes match.

| Gate | Elapsed time | Dune workers | Peak child RSS |
| --- | ---: | ---: | ---: |
| `check-fast` | 670.887 seconds | 2 | 2324228 KiB |
| `check-iris` | 2397.156 seconds | 2 | 984096 KiB |

The sandbox hid other projects under `/home/cody`.
It exposed the clone and the declared host directories.
The host operating-system tree remained read-only.
The runtime used writable `/tmp`, `/dev`, and `/run/user/1000/zesu-guard`.
The EVM-Sail reference checkout was a pinned, read-only host input.
`BUILD.md` gives its retrieval commands and the source hashes.

A separate syscall audit checked the production manifest command.
This audit checked 9325 artifacts and 79 inputs.
It observed 31507 read-capable opens across 11826 unique paths.
It found no undeclared paths under `/home`.
The full gates ran without syscall tracing.
The syscall audit does not cover every gate process.

`p0e-condition10-isolated.json` records exact commands, allowed paths, hashes, source revisions, measurements, and archived logs.
The 74d4a2e6 clone gates remain prior-revision evidence.
The cross-host runtime retrieval and complete toolchain lock remain documented gaps.
