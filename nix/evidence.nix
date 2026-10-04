{ pkgs, endpointElf }:
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
in {
  inherit cfg;
}
