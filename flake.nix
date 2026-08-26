{
  description = "Rocq and Islaris verification of the Zesu SSZ decoder";

  inputs = {
    binaryFv.url = "github:codygunton/binary-fv-experiment/38a3a14a";
    nixpkgs.follows = "binaryFv/nixpkgs";
    evmSail.follows = "binaryFv/evmSail";
    evmSailCompiler.follows = "binaryFv/evmSailCompiler";
  };

  outputs = { self, binaryFv, nixpkgs, evmSail, evmSailCompiler }:
    let
      systems = [ "x86_64-linux" ];
      forAllSystems = nixpkgs.lib.genAttrs systems;
    in {
      packages = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; };
          endpointElf = binaryFv.packages.${system}.zesuSszDecodeRv64Elf;
          evidence = import ./nix/evidence.nix {
            inherit pkgs endpointElf;
            smokeInputs = binaryFv.packages.${system}.zesuSszDecodeSmoke;
          };
          viewerUi = import ./nix/viewer.nix { inherit pkgs; };
        in {
          endpoint-elf = endpointElf;
          endpoint-cfg = evidence.cfg;
          coarse-contract-manifest = evidence.manifest;
          coarse-contract-bindings = evidence.bindings;
          coarse-contract-evidence = evidence.evidence;
          viewer = viewerUi;
          default = endpointElf;
        });

      checks = forAllSystems (system: {
        endpoint-elf = self.packages.${system}.endpoint-elf;
        endpoint-cfg = self.packages.${system}.endpoint-cfg;
        coarse-contract-evidence = self.packages.${system}.coarse-contract-evidence;
        viewer = self.packages.${system}.viewer;
      });
    };
}
