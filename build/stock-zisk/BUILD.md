# Stock build gates

The retained production targets depend on the stock native indexes.
`make check-fast` and `make check-iris` restore or regenerate these indexes before Dune starts.
The factory checks the files and commitments against `build-recipe.json`.
The Makefile creates the selected build directories before Dune starts.

The default dataset cache is `_build/stock-zisk/native-trace-cache` in each worktree.
Worktrees do not share this cache by default.
Set `STOCK_NATIVE_TRACE_CACHE_DIR` to use a shared cache:

```sh
make check-fast STOCK_NATIVE_TRACE_CACHE_DIR=/path/to/shared/native-trace-cache
```

The cache key uses the canonical file hashes.
It excludes paths, identity fields, and measurements.
The factory checks a cache entry before restoration.
An empty cache causes native trace generation from the pinned ELF and model.
The factory checks generated files before installation.
The per-instruction cache lives in `generated/isla-traces/stock-zisk` in each worktree.
The dataset cache excludes generation measurements.

Keep legacy fork trace directories outside the Dune source tree.
`dune build @all` also builds ignored directories that contain Dune theories.

The stock manifest uses paths relative to the project root for project files.
Run the gates from the checkout root.
The artifact identity does not depend on the checkout location.
A clone uses its own tools, build artifacts, wrappers, and generated traces.

The following steps reproduce the gates on this host:

```sh
python3 tools/stock_zisk/fetch_inputs.py
make check-fast CHECK_AGENT=worker-build-2-e FAST_JOBS=2 STOCK_NATIVE_TRACE_CACHE_DIR=/home/cody/zesislar-archive/stock-inputs/native-trace-cache
make check-iris CHECK_AGENT=worker-build-2-e FAST_JOBS=2 AGENT_JOBS=2 STOCK_NATIVE_TRACE_CACHE_DIR=/home/cody/zesislar-archive/stock-inputs/native-trace-cache
```

The fetch command verifies pinned source revisions and all declared input hashes.
It fetches missing source checkouts from the upstream repositories.
All three pinned checkouts use project-relative paths under `_build`.
It copies the stock object from the declared host archive when the object is absent.
It does not change the manifest or artifact identity.
The cache is optional.
The trace factory verifies its contents before restoration.
An absent cache causes generation from the pinned ELF and model.

The declared host archive is `/home/cody/zesislar-archive/stock-inputs`.
The runtime file is `f119db4b30124f276483679d2ccf7c1089bb1d51b16bfc172e082e206693e491-libziskos_staticlib.a`.
Its SHA-256 is `f119db4b30124f276483679d2ccf7c1089bb1d51b16bfc172e082e206693e491`.
The selected object file is `dcd4b1bec1b02f94d7c4bca3d8323c386cfc7b780995235d6947790bb68d1afe-zesu.o`.
Its SHA-256 is `dcd4b1bec1b02f94d7c4bca3d8323c386cfc7b780995235d6947790bb68d1afe`.
The compiler and Coq plugin use their hash-prefixed names in this archive.
The manifest gives their exact paths and SHA-256 hashes.
The host must retain the declared archive files and toolchain executables.
`fetch_inputs.py` checks these host requirements.

`p0e-condition10-retrieval.json` documents the original 76 project files.
It records the exact runtime retrieval step on this host.
The runtime container ID lacks a registry reference.
The cross-host runtime retrieval and complete toolchain lock remain documented gaps.
This procedure claims reproduction on this host only.
