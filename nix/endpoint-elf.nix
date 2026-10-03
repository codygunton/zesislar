{ pkgs, endpointElf }:
pkgs.runCommand "zesu-ssz-endpoint-elf" { } ''
  cp -a ${endpointElf} "$out"
  chmod -R u+w "$out"
  mv "$out/meta/disassembly.txt" "$out/meta/disassembly.objdump"
  sed -i 's/disassembly\.txt/disassembly.objdump/g' "$out/meta/provenance.txt"
''
