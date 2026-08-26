{ pkgs, endpointElf, smokeInputs }:
let
  python = pkgs.python3.withPackages (ps: [ ps.capstone ps.pyelftools ]);
  tools = builtins.path {
    path = ../ZesuSsz/Evidence;
    name = "zesislar-evidence-tools";
  };

  cfg = pkgs.runCommand "zesislar-zesu-cfg" { nativeBuildInputs = [ python ]; } ''
    mkdir -p "$out" repeated
    export PYTHONPATH=${tools}
    python ${tools}/generate_zesu_cfg.py \
      --object ${endpointElf}/bin/zesu-ssz-decode \
      --output "$out/zesu-cfg.json" \
      --flame "$out/flame.json" \
      --proof-map "$out/proof-map.json"
    python ${tools}/test_zesu_cfg.py "$out/zesu-cfg.json"
    python ${tools}/test_source_path_normalization.py
    python ${tools}/generate_zesu_cfg.py \
      --object ${endpointElf}/bin/zesu-ssz-decode \
      --output repeated/zesu-cfg.json \
      --flame repeated/flame.json \
      --proof-map repeated/proof-map.json
    cmp "$out/zesu-cfg.json" repeated/zesu-cfg.json
    cmp "$out/flame.json" repeated/flame.json
    cmp "$out/proof-map.json" repeated/proof-map.json
  '';

  manifest = pkgs.runCommand "zesislar-coarse-contract-manifest" {
    nativeBuildInputs = [ python ];
  } ''
    mkdir -p "$out"
    python ${tools}/generate_level_manifest.py \
      --cfg ${cfg}/zesu-cfg.json --flame ${cfg}/flame.json \
      --level 1 --output "$out/contracts.json"
    python ${tools}/test_level_manifest.py "$out/contracts.json"
    PYTHONPATH=${tools} python ${tools}/check_coarse_contracts.py "$out/contracts.json"
  '';

  bindings = pkgs.runCommand "zesislar-coarse-contract-bindings" {
    nativeBuildInputs = [ python ];
  } ''
    mkdir -p "$out"
    python ${tools}/generate_level_boundary_bindings.py \
      --manifest ${manifest}/contracts.json \
      --elf ${endpointElf}/bin/zesu-ssz-decode \
      --output "$out/bindings.json"
    python ${tools}/test_level_boundary_bindings.py "$out/bindings.json"
  '';

  evidence = pkgs.runCommand "zesislar-coarse-contract-evidence" {
    nativeBuildInputs = [ pkgs.gcc pkgs.glib pkgs.pkg-config python pkgs.qemu-user ];
  } ''
    set -euo pipefail
    export PYTHONPATH=${tools}
    python -m unittest discover -s ${tools} -p 'test_*.py'
    gcc -shared -fPIC -O2 -Wall -Wextra -Werror \
      -I${pkgs.qemu-user}/include $(pkg-config --cflags glib-2.0) \
      ${tools}/qemu_trace_plugin.c -o trace.so
    snapshots=$(python -c 'import json; rows=json.load(open("${manifest}/contracts.json"))["instances"]; cfg=json.load(open("${cfg}/zesu-cfg.json")); main=next(row for row in cfg["functionInstances"] if row["kind"] == "concrete" and row["name"] == "ssz_decode_root.main"); pcs=sorted({pc for row in rows for pc in row["executionPcs"]} | {row["entryPc"] for row in rows} | set(main["pcs"])); print(",".join("snapshot="+str(pc) for pc in pcs))')
    for vector in minimal invalid; do
      qemu-riscv64 \
        -plugin ./trace.so,out="$vector.trace",input=${smokeInputs}/"$vector.ssz",input_address=0x2001a000,context_address=0x2401a0b8,terminal=0x101d0,capture_write=0x10190,capture_window=0x14d30,capture_window_width=848,"$snapshots" \
        ${endpointElf}/bin/zesu-ssz-decode
    done
    mkdir -p "$out"
    python ${tools}/analyze.py \
      --manifest ${manifest}/contracts.json --bindings ${bindings}/bindings.json \
      --elf ${endpointElf}/bin/zesu-ssz-decode \
      --trace minimal=minimal.trace --trace invalid=invalid.trace \
      --input minimal=${smokeInputs}/minimal.ssz --input invalid=${smokeInputs}/invalid.ssz \
      --output "$out/evidence.json"
  '';
in {
  inherit bindings cfg evidence manifest;
}
