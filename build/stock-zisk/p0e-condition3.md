# P0-E condition 3

I checked all 55 removed files against the archived Git blobs.
`p0e-condition3-archive.json` gives each path, SHA-256 hash, archive location, and immutable commit.

Proposal: Keep the harness set because the stock block harness invokes its tools.
The original 582-file label now covers 490 tracked files.
This proposal does not assert that each historical dataset is a required dependency.

`build/stock-zisk/q4-q9/REPORT.json` binds `tools/det/infer_boundary.py` and `tools/det/gen_boundary.py`.
`tools/block/blockrun.py` imports `infer_boundary` from `tools/det` and modules from `tools/residual`.
`tools/block/gen_block.py` invokes `tools/det/gen_segment.py`.

- `tools/det` contains 28 tracked files.
- `tools/residual` contains 21 tracked files.
- `tools/fixtures` contains 3 tracked files.
- `ZesuSsz/Evidence/det` contains 355 tracked files.
- `ZesuSsz/Evidence/residuals` contains 83 tracked files.
