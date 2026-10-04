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
