{
  description = "Rocq and Islaris verification of the Zesu SSZ decoder";

  inputs = {
    binaryFv.url = "github:codygunton/binary-fv-experiment/38a3a14a";
    nixpkgs.follows = "binaryFv/nixpkgs";
    evmSail.follows = "binaryFv/evmSail";
    evmSailCompiler.follows = "binaryFv/evmSailCompiler";
    zesu = {
      flake = false;
      follows = "binaryFv/zesu";
    };
  };

  outputs = { self, binaryFv, nixpkgs, evmSail, evmSailCompiler, zesu }:
    let
      systems = [ "x86_64-linux" ];
      forAllSystems = nixpkgs.lib.genAttrs systems;
    in {
      packages = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; };
          endpointElf = binaryFv.packages.${system}.zesuSszDecodeRv64Elf;
          target = import ./nix/target.nix {
            inherit pkgs endpointElf;
            zesuSource = zesu;
          };
          evidence = import ./nix/evidence.nix {
            inherit pkgs endpointElf;
            smokeInputs = binaryFv.packages.${system}.zesuSszDecodeSmoke;
          };
          viewerUi = import ./nix/viewer.nix { inherit pkgs; };
        in {
          endpoint-elf = endpointElf;
          endpoint-entry-dump = target.entryDump;
          zesu-source = target.source;
          endpoint-cfg = evidence.cfg;
          level1-contract-manifest = evidence.manifest;
          level1-contract-bindings = evidence.bindings;
          level1-contract-evidence = evidence.evidence;
          viewer = viewerUi;
          default = endpointElf;
        });

      apps = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; };
          target = import ./nix/target.nix {
            inherit pkgs;
            endpointElf = binaryFv.packages.${system}.zesuSszDecodeRv64Elf;
            zesuSource = zesu;
          };
        in {
          link-zesu-source = {
            type = "app";
            program = "${target.sourceLink}/bin/link-zesu-source";
          };
        });

      checks = forAllSystems (system: {
        endpoint-elf = self.packages.${system}.endpoint-elf;
        endpoint-entry-dump = self.packages.${system}.endpoint-entry-dump;
        zesu-source = self.packages.${system}.zesu-source;
        endpoint-cfg = self.packages.${system}.endpoint-cfg;
        level1-contract-evidence = self.packages.${system}.level1-contract-evidence;
        viewer = self.packages.${system}.viewer;
      });
    };
}
