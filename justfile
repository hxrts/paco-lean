# Paco-Lean build recipes

# Default recipe: full build
default: build

# Full build
build:
    lake build

# Quick build for core paco modules
quick:
    lake build Paco.Basic Paco.UpTo.Compat Paco.UpTo.Closures Paco.Companion

# Build tests
test:
    lake build Tests

# Clean build artifacts
clean:
    lake clean

# Update dependencies
update:
    lake update
