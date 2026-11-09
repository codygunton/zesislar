#!/usr/bin/env bash
set -euo pipefail

# Stable Dune entry point. Dune copies this file to tools/guard-bin/coqc and
# digests it into the cache key of every compile, so it only finds and execs
# the routing script beside it. Guard changes must go to dune_coqc_route.sh
# (or the guard itself): they then leave every compile cache key unchanged.
tools_dir=$(dirname "$(realpath "$0")")
if [[ "$(basename "$tools_dir")" == guard-bin ]]; then
  tools_dir=$(dirname "$tools_dir")
fi
exec "$tools_dir/dune_coqc_route.sh" "$@"
