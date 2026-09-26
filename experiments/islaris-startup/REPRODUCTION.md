# Approved startup traces

The user approved these three startup traces on 2026-09-25.
Their PCs are `0x10120`, `0x10124`, and `0x10128`.
The profile covers `[0x10120, 0x1012c)`.
The pinned ELF, Islaris, trace generator, and configuration remain unchanged.

I read the existing files in `.worktrees/orch-endpoint-preview/generated/isla-traces/startup`.
The preview HEAD was `0b1286668614c3608611042a7e32619e7990e49c` during this inspection.
I did not regenerate traces for this record.
The earlier endpoint preview at `264096af` passed `check-fast` and `check-iris`.

## Inputs

The ELF is `build/endpoint-elf/bin/zesu-ssz-decode`.
Its Nix output is `/nix/store/6p2b45b0k1403dqimlprgnllw68y6wyi-zesu-ssz-decode-bare-metal-rv64im-elf-d67f28c`.
The provenance identifies `codygunton/zesu@d67f28c`.
The dump selects the single `riscv64_zesu.toml` configuration.
The repository and installed configuration hashes are equal.

| Input | SHA-256 |
|---|---|
| `build/endpoint-elf/bin/zesu-ssz-decode` | `3e13afeae5719e10c65a89ea1b8a9afdb60b360e7e18faa81c31a71a44dcd8fb` |
| `build/endpoint-elf/meta/disassembly.txt` | `80d0a3bcdfabbe99156a62efbc9470a40f3c55b39388c3de6112aa3a42d73fad` |
| `ZesuSsz/riscv64_zesu.toml` | `76a2a8f4896670b9e7c7651731abf696b2429af7863a5f07f735f8b7a006c297` |
| `/home/cody/islaris/_opam/etc/islaris/riscv64_zesu.toml` | `76a2a8f4896670b9e7c7651731abf696b2429af7863a5f07f735f8b7a006c297` |
| `ZesuSsz/Evidence/generate_islaris_dump.py` | `0436cf8899814946746b2f0bd4a67d5294943a06bb5f0071dfabed6fad4360c8` |
| `experiments/islaris-startup/profile.json` | `fd77a8189ef39c2940f13486e3a7d90ec9cf40cc46ea8d973eb4e9eaeac00167` |
| `build/islaris-dumps/startup.dump` | `5f5419c34a35609d33007eed1560eb674001dedfb341c35feee962b49edb0ac7` |

## Makefile commands

These commands expand the startup Makefile targets with the current default paths.
The generator writes the dump from the pinned disassembly.
Islaris writes the eight files listed below.
The final command removes the package field and adds the Dune dependencies.

```sh
python3 ZesuSsz/Evidence/generate_islaris_dump.py \
  --disassembly build/endpoint-elf/meta/disassembly.txt \
  --profile experiments/islaris-startup/profile.json \
  --output build/islaris-dumps/startup.dump

mkdir -p generated/isla-traces/startup
opam exec --switch=/home/cody/islaris -- islaris \
  build/islaris-dumps/startup.dump -j 3 \
  -o generated/isla-traces/startup \
  --coqdir=IslaTraces.startup --arch=riscv64

sed -i -e '/(package islaris)/d' \
  -e 's/(theories isla isla.riscv64)/(theories isla isla.riscv64 InstrSpecs lithium iris stdpp RecordUpdate Ltac2)/' \
  generated/isla-traces/startup/dune
```

## Generated files

All paths in this table are relative to `generated/isla-traces/startup/`.
The generated files remain ignored outputs.

| File | SHA-256 |
|---|---|
| `a10120.isla` | `754e824ed4fd1fb99dbb38e3d2f835b6758dd3f9f847849d437e53dd99c6b949` |
| `a10120.v` | `a9b247e6c8c2121785b10f08d6cbf3273277b5853de7fd323c9b75aafc3c18cf` |
| `a10124.isla` | `b9670096b1a980b9ea8cabab5bc27bd0d07b45a412953469bc28b71d0c9475d4` |
| `a10124.v` | `5647b0359c1c7f710a82bddbe8db5af86557adf94ea8d201e2ec3948ac14540c` |
| `a10128.isla` | `2e593d282b19794986a21949d043b7f2d330d8a1034005579ca7ed60555201c4` |
| `a10128.v` | `19873cf46f8cccee6931aa7ecf3ab17500412285e05ac1b3b4c06224a6a7526b` |
| `dune` | `76844e53f8c539e6e9c76e6c4d97864edd90249efb6c0f7d650b6f54a2b6b258` |
| `instrs.v` | `cb294d5d325679b338268f44159c3b03560e812147ecf66e3cfb91895dee8454` |
