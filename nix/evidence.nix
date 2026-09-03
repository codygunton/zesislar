{ pkgs, endpointElf, smokeInputs }:
let
  python = pkgs.python3.withPackages (ps: [ ps.capstone ps.pyelftools ]);
  tools = builtins.path {
    path = ../ZesuSsz/Evidence;
    name = "zesu-ssz-evidence";
  };

  cfg = pkgs.runCommand "zesu-ssz-cfg" { nativeBuildInputs = [ python ]; } ''
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

  manifest = pkgs.runCommand "zesu-ssz-level1-contract-manifest" {
    nativeBuildInputs = [ python ];
  } ''
    mkdir -p "$out"
    python ${tools}/generate_level_manifest.py \
      --cfg ${cfg}/zesu-cfg.json --flame ${cfg}/flame.json \
      --level 1 --output "$out/contracts.json"
    python ${tools}/test_level_manifest.py "$out/contracts.json"
    PYTHONPATH=${tools} python ${tools}/check_level1_contracts.py "$out/contracts.json"
  '';

  bindings = pkgs.runCommand "zesu-ssz-level1-contract-bindings" {
    nativeBuildInputs = [ python ];
  } ''
    mkdir -p "$out"
    python ${tools}/generate_level_boundary_bindings.py \
      --manifest ${manifest}/contracts.json \
      --elf ${endpointElf}/bin/zesu-ssz-decode \
      --output "$out/bindings.json"
    python ${tools}/test_level_boundary_bindings.py "$out/bindings.json"
  '';

  rocq = pkgs.runCommand "zesu-ssz-level1-contract-rocq" {
    nativeBuildInputs = [ python ];
  } ''
    mkdir -p "$out/ZesuSsz/Generated"
    export PYTHONPATH=${tools}
    python ${tools}/test_generate_level1_rocq.py
    python ${tools}/generate_level1_rocq.py \
      --manifest ${manifest}/contracts.json \
      --cfg ${cfg}/zesu-cfg.json \
      --output "$out/ZesuSsz/Generated/Level1.v"
    cmp "$out/ZesuSsz/Generated/Level1.v" ${../ZesuSsz/Generated/Level1.v}
  '';

  evidence = pkgs.runCommand "zesu-ssz-level1-contract-evidence" {
    nativeBuildInputs = [ pkgs.gcc pkgs.glib pkgs.pkg-config python pkgs.qemu-user ];
  } ''
    set -euo pipefail
    export PYTHONPATH=${tools}
    export ZESU_SSZ_ROOT=${../.}
    python -m unittest discover -s ${tools} -p 'test_*.py'
    gcc -shared -fPIC -O2 -Wall -Wextra -Werror \
      -I${pkgs.qemu-user}/include $(pkg-config --cflags glib-2.0) \
      ${tools}/qemu_trace_plugin.c -o trace.so
    snapshots=$(python -c 'import json; rows=json.load(open("${manifest}/contracts.json"))["instances"]; cfg=json.load(open("${cfg}/zesu-cfg.json")); main=next(row for row in cfg["functionInstances"] if row["kind"] == "concrete" and row["name"] == "ssz_decode_root.main"); pcs=sorted({pc for row in rows for pc in row["executionPcs"]} | {row["entryPc"] for row in rows} | set(main["pcs"])); print(",".join("snapshot="+str(pc) for pc in pcs))')
    run_vectors() {
      prefix="$1"
      for vector in minimal invalid; do
        env -i ${pkgs.qemu-user}/bin/qemu-riscv64 \
          -plugin ./trace.so,out="$prefix-$vector.trace",input=${smokeInputs}/"$vector.ssz",input_address=0x2001a000,context_address=0x2401a0b8,terminal=0x101d0,capture_write=0x10190,capture_window=0x14d30,capture_window_width=848,"$snapshots" \
          ${endpointElf}/bin/zesu-ssz-decode
      done
    }
    run_vectors first
    run_vectors second
    cmp first-minimal.trace second-minimal.trace
    cmp first-invalid.trace second-invalid.trace
    mkdir -p "$out"
    analyze() {
      prefix="$1"
      output="$2"
      python ${tools}/analyze.py \
        --manifest ${manifest}/contracts.json --bindings ${bindings}/bindings.json \
        --elf ${endpointElf}/bin/zesu-ssz-decode \
        --trace minimal="$prefix-minimal.trace" --trace invalid="$prefix-invalid.trace" \
        --input minimal=${smokeInputs}/minimal.ssz --input invalid=${smokeInputs}/invalid.ssz \
        --output "$output"
    }
    analyze first first-evidence.json
    analyze second second-evidence.json
    cmp first-evidence.json second-evidence.json
    cp first-evidence.json "$out/evidence.json"
    cp first-minimal.trace "$out/minimal.trace"
    cp first-invalid.trace "$out/invalid.trace"
    check_contract() {
      script="$1"
      spec="$2"
      output="$3"
      PYTHONPATH=${../ZesuSsz/Evidence} python "$script" \
        --spec "$spec" \
        --manifest ${manifest}/contracts.json \
        --bindings ${bindings}/bindings.json \
        --evidence "$out/evidence.json" \
        --output "$out/$output"
    }
    check_contract ${../ZesuSsz/Evidence/check_read_input_contract.py} \
      ${../contracts/level1-read-input-evidence.json} read-input-contract.json
    check_contract ${../ZesuSsz/Evidence/check_allocator_get_contract.py} \
      ${../contracts/level1-allocator-get-evidence.json} allocator-get-contract.json
    check_contract ${../ZesuSsz/Evidence/check_decode_contract.py} \
      ${../contracts/level1-decode-evidence.json} ssz-decode-contract.json
    check_contract ${../ZesuSsz/Evidence/check_write_success_contract.py} \
      ${../contracts/level1-write-success-evidence.json} write-success-contract.json
    check_contract ${../ZesuSsz/Evidence/check_write_failure_contract.py} \
      ${../contracts/level1-write-failure-evidence.json} write-failure-contract.json
    check_contract ${../ZesuSsz/Evidence/check_zkvm_exit_contract.py} \
      ${../contracts/level1-zkvm-exit-evidence.json} zkvm-exit-contract.json
  '';

  viewerData = pkgs.runCommand "zesu-ssz-level1-viewer-data" {
    nativeBuildInputs = [ python ];
  } ''
    mkdir -p "$out"
    export PYTHONPATH=${tools}:${../ZesuSsz/Viewer}
    python ${tools}/build_flame_ui_data.py \
      --input ${cfg}/flame.json \
      --core "$out/flame-core.json" --details "$out/flame-details.json"
    python ${tools}/build_level1_proof_map.py \
      --cfg ${cfg}/zesu-cfg.json --flame ${cfg}/flame.json \
      --manifest ${manifest}/contracts.json --evidence ${evidence}/evidence.json \
      --bindings ${bindings}/bindings.json --progress ${../contracts/viewer-progress.json} \
      --output "$out/proof-map.json" --flame-progress-output "$out/flame-progress.json"
    python ${tools}/check_level1_proof_map.py \
      --proof-map "$out/proof-map.json" --manifest ${manifest}/contracts.json \
      --evidence ${evidence}/evidence.json --bindings ${bindings}/bindings.json
    python ${../ZesuSsz/Viewer/build_zesu_speedscope.py} \
      --core "$out/flame-core.json" --progress "$out/flame-progress.json" \
      --details-input "$out/flame-details.json" \
      --scope decode --details-url flame-details.json \
      --output "$out/zesu-decode.speedscope.json"
    cp ${manifest}/contracts.json "$out/level1-manifest.json"
    cp ${bindings}/bindings.json "$out/level1-boundary-bindings.json"
    cp ${evidence}/evidence.json "$out/level1-evidence.json"
    cp ${evidence}/*-contract.json "$out/"
  '';
in {
  inherit bindings cfg evidence manifest rocq viewerData;
}
