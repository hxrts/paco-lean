# Setup Guide

This guide covers installation and configuration of paco-lean.

## Prerequisites

You need Lean 4.26.0 or later and the Lake build tool. See the [Lean 4 installation guide](https://lean-lang.org/lean4/doc/setup.html) for setup instructions.

Alternatively, use the provided Nix flake. Run `nix develop` from the repository root to enter a development shell with the correct Lean version pre-configured.

```bash
nix develop
```

The flake handles toolchain management automatically.

## Installation

Add paco-lean to your project by modifying `lakefile.lean`. Include the following require statement.

```lean
require paco from git
  "https://github.com/hxrts/paco-lean.git"@"main"
```

The `@"main"` specifies the branch to use.

## Building

Run `lake build` from your project root to compile the library.

```bash
lake build
```

Lake will download mathlib and other dependencies on first build. This process may take 5-15 minutes depending on your connection speed and whether mathlib cache is available. Subsequent builds are much faster.

## Running Tests

The test suite validates the library functions correctly. Run tests with the following command.

```bash
lake build Tests
```

All tests should pass without errors. If tests fail, ensure your dependencies are up to date by running `lake update`.

## Troubleshooting

### Mathlib Cache Issues

If you encounter errors like "failed to load header" or corruption messages, clear the build cache.

```bash
lake clean
lake build
```

This removes all compiled artifacts and rebuilds from scratch.

### Dependency Updates

When mathlib or other dependencies change, update your local copies.

```bash
lake update
lake build
```

This fetches the latest versions specified in your lakefile.

## Next Steps

See [Theoretical Foundations](02-theory.md) for the mathematical concepts behind paco. See [Architecture Guide](03-architecture.md) for an overview of the module structure. See [Basic Usage Tutorial](04-basic-usage.md) for a tutorial on writing coinductive proofs.
