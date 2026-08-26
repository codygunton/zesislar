{ pkgs }:

pkgs.buildNpmPackage {
  pname = "zesislar-speedscope";
  version = "1.25.0";
  src = ../tools/viewer/speedscope;
  npmDepsHash = "sha256-hgvO5iU9lerTa9FJRHq9lm67lgrFSM5AR02GShsM3P8=";
  dontNpmBuild = true;
  installPhase = ''
    runHook preInstall
    node_modules/.bin/tsx scripts/build-release.ts --outdir "$out" --protocol http
    cp assets/source-code-pro/LICENSE.md "$out/source-code-pro.LICENSE.md"
    cp LICENSE "$out/speedscope.LICENSE"
    runHook postInstall
  '';
}
