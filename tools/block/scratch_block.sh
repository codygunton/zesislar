#!/usr/bin/env bash
set -euo pipefail

script_dir=$(dirname "$(realpath "$0")")
exec python3 "$script_dir/scratch_block.py" "$@"
