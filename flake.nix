{
  description = "FIR: a formally specified compiler IR";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

  outputs =
    { self, nixpkgs }:
    let
      # Linux (x86_64 and ARM, including WSL2 on Windows) and Apple Silicon macOS.
      # Intel macOS is absent because nixpkgs stopped building x86_64-darwin in 26.11.
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "aarch64-darwin"
      ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in
    {
      devShells = forAllSystems (pkgs: {
        default = import ./nix/devshell.nix { inherit pkgs; };
      });

      # Build every dev shell in `nix flake check`, so CI catches a broken toolchain per platform.
      checks = forAllSystems (pkgs: {
        devshell = self.devShells.${pkgs.stdenv.hostPlatform.system}.default;
      });

      formatter = forAllSystems (pkgs: pkgs.nixfmt-tree);
    };
}
