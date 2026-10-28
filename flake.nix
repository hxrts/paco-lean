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

        leanToolchain =
          pkgs.lib.strings.removeSuffix "\n" (builtins.readFile ./lean-toolchain);

        nativeBuildInputs = with pkgs; [
          # Lean
          elan

          # Build tools
          just
          python3

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
            export ELAN_TOOLCHAIN="${leanToolchain}"

            # Default Lake's artifact cache on; a caller's explicit
            # LAKE_ARTIFACT_CACHE or LAKE_CACHE_DIR always wins.
            export LAKE_ARTIFACT_CACHE="''${LAKE_ARTIFACT_CACHE:-true}"

            # Keep cached artifacts materialized under .lake/build so the
            # `test -f` guards in the justfile keep working.
            export LAKE_RESTORE_ARTIFACTS="''${LAKE_RESTORE_ARTIFACTS:-true}"

            # Let Lake restore prebuilt mathlib artifacts from the shared cache
            # before mathlib's post-update hook downloads them again.
            export MATHLIB_NO_CACHE_ON_UPDATE="''${MATHLIB_NO_CACHE_ON_UPDATE:-1}"

            # Join the machine-local shared artifact cache when a sibling
            # lean-builder checkout provides one. Absent for other contributors,
            # who then get Lake's own default cache.
            if [ -f ../lean-builder/env.sh ]; then
              . ../lean-builder/env.sh
            fi

            echo "Paco development environment"
            echo "Lean: ${leanToolchain}"
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
