{
  description = "Paco - Parametrized Coinduction for Lean 4";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };

        nativeBuildInputs = with pkgs; [
          # Lean
          elan

          # Build tools
          just

          # Documentation
          mdbook
          mdbook-mermaid
          mdbook-toc

          # Link checking
          lychee

          # Shell utilities for scripts
          coreutils
          findutils
          gawk
          gnused
        ];

      in
      {
        devShells.default = pkgs.mkShell {
          inherit nativeBuildInputs;

          shellHook = ''
            echo "Paco development environment"
            echo "Lean: $(elan show 2>/dev/null | head -1 || echo 'run: elan default leanprover/lean4:v4.26.0')"
            echo ""
            echo "Commands:"
            echo "  just build      - Build the project"
            echo "  just book       - Build documentation"
            echo "  just serve      - Serve docs with live reload"
            echo "  just link-check - Check for broken links"
          '';
        };
      }
    );
}
