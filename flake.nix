{
  description = "Lean Together 2024 bv_decide ";

  inputs.utils.url = "github:numtide/flake-utils";
  inputs.nixpkgs.url = "github:nixos/nixpkgs/24.11-beta";

  outputs = {
    nixpkgs,
    utils,
    ...
  }:
    utils.lib.eachDefaultSystem (system: let
      pkgs = import nixpkgs { system = system; config.allowUnfree = true; };
      typst-shell = pkgs.mkShell {
        nativeBuildInputs = [
          pkgs.tinymist
          pkgs.typst
        ];
      };
    in {
      devShells.default = typst-shell;
      legacyPackages = pkgs;
    });
}
