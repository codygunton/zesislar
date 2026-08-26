{ pkgs, endpointElf, zesuSource }:
let
  entryPcs = [ "10140" "101c4" "12168" "14ccc" "14d30" "161c0" ];

  sourceLink = pkgs.writeShellApplication {
    name = "link-zesu-source";
    text = ''
      target="$PWD/verification-target/zesu"
      mkdir -p "$PWD/verification-target"
      if [[ -L "$target" ]]; then
        unlink "$target"
      elif [[ -e "$target" ]]; then
        echo "$target is not a symbolic link" >&2
        exit 1
      fi
      ln -s ${zesuSource} "$target"
      echo "$target -> ${zesuSource}"
    '';
  };

  source = pkgs.runCommand "zesu-source-d67f28c" { } ''
    ln -s ${zesuSource} "$out"
  '';

  entryDump = pkgs.runCommand "zesu-ssz-level1-entry-dump" {
    nativeBuildInputs = [ pkgs.llvm pkgs.python3 ];
  } ''
    llvm-objdump -d ${endpointElf}/bin/zesu-ssz-decode > disassembly.txt
    python ${./select-entry-instructions.py} \
      --disassembly disassembly.txt \
      --output entrypoints.dump \
      ${builtins.concatStringsSep " " entryPcs}
    mkdir -p "$out"
    cp entrypoints.dump "$out/entrypoints.dump"
  '';
in {
  inherit entryDump source sourceLink;
}
