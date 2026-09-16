#!/usr/bin/env bash
set -euo pipefail

common_dir=$(git rev-parse --path-format=absolute --git-common-dir)
base_dir=$(dirname "$common_dir")
before_bytes=$(df --output=avail -B1 /home | tail -n 1 | tr -d ' ')

remove_worktree() {
  local name=$1
  local path="$base_dir/.worktrees/$name"
  local head

  if ! git -C "$base_dir" worktree list --porcelain | grep -Fxq "worktree $path"; then
    return
  fi

  head=$(git -C "$path" rev-parse HEAD)
  if ! git -C "$base_dir" branch -r --contains "$head" | grep -q .; then
    printf 'Skip unpushed worktree: %s\n' "$name" >&2
    return
  fi

  git -C "$base_dir" worktree remove --force "$path"
}

historical_worktrees=(
  islaris-proof-foundation
  islaris-read-input-pr
  islaris-write-success-monolithic
  islaris-zkvm-exit
)

transient_worktrees=(
  islaris-native-orch-preview
  islaris-native-orch-repair
  islaris-native-orch-repair2
  islaris-native-orch-contract
  islaris-native-backup
  islaris-native-tx-step8
  islaris-native-tail-repair-step8
)

for name in "${historical_worktrees[@]}" "${transient_worktrees[@]}"; do
  remove_worktree "$name"
done

git -C "$base_dir" worktree prune

stale_builds=(push1 push2 nightly orch-preview orch-repair orch-repair2 orch-contract backup tx-step8 tail-repair tail-repair-step8)
mapfile -t worktree_paths < <(
  git -C "$base_dir" worktree list --porcelain |
    sed -n 's/^worktree //p'
)
for worktree_path in "${worktree_paths[@]}"; do
  for name in "${stale_builds[@]}"; do
    rm -rf "$worktree_path/_build/agents/$name"
  done
done

if command -v dune >/dev/null 2>&1; then
  dune cache trim --size=20GB
else
  opam exec --switch=/home/cody/islaris -- dune cache trim --size=20GB
fi

after_bytes=$(df --output=avail -B1 /home | tail -n 1 | tr -d ' ')
freed_bytes=$((after_bytes - before_bytes))
awk -v bytes="$freed_bytes" 'BEGIN { printf "Freed: %.2f GiB\n", bytes / 1073741824 }'
df -h /home
printf 'Worktrees: %s\n' "$(git -C "$base_dir" worktree list --porcelain | grep -c '^worktree ')"
