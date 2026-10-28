# Paco-Lean build recipes

# ─────────────────────────────────────────────────────────────────────────────
# Configuration
# ─────────────────────────────────────────────────────────────────────────────

# `lean-toolchain` is the single source of truth, so every recipe runs the
# Lean and Lake that file names even when the shell selected another.
export ELAN_TOOLCHAIN := `tr -d '\r\n' < lean-toolchain`

# Worker count for a degraded, uncoordinated run. When a sibling lean-builder
# coordinator is available it grants the count instead.
export LEAN_NUM_THREADS := env_var_or_default("LEAN_NUM_THREADS", "3")

lean_build := "python3 tools/run_lean_build.py"

# ─────────────────────────────────────────────────────────────────────────────
# Build
# ─────────────────────────────────────────────────────────────────────────────

# Default recipe: full build
default: build

# Restore mathlib from Lake's configured cache first; on a genuine miss, fall
# back to mathlib's prebuilt cache. Never compiles mathlib.
_mathlib-cache:
    @if [ ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean ]; then lake build Mathlib --no-build >/dev/null 2>&1 || true; fi
    @if [ ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean ]; then {{lean_build}} --label "fetch mathlib cache" -- lake exe cache get; fi
    @test -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean || { echo "mathlib cache missing" >&2; exit 1; }

# Full build
build: _mathlib-cache
    {{lean_build}} --label "build Paco" -- lake build

# Quick build for core paco modules
quick: _mathlib-cache
    {{lean_build}} --label "build Paco core" -- lake build Paco.Basic Paco.UpTo.Compat Paco.UpTo.Closures Paco.Companion

# Build tests
test: _mathlib-cache
    {{lean_build}} --label "build Tests" -- lake build Tests

# Reject Lake build recipes that skip the launcher
check-launcher:
    python3 tools/check_build_launcher.py

# Clean build artifacts
clean:
    lake clean
    rm -rf docs/book

# Update dependencies
update:
    lake update

# ─────────────────────────────────────────────────────────────────────────────
# Documentation
# ─────────────────────────────────────────────────────────────────────────────

# Auto-generate SUMMARY.md from docs directory
summary:
    #!/usr/bin/env bash
    set -euo pipefail

    docs="docs"
    build_dir="$docs/book"
    out="$docs/SUMMARY.md"

    echo "# Summary" > "$out"
    echo "" >> "$out"

    # Find all .md files under docs/, excluding SUMMARY.md itself and the build output
    while IFS= read -r f; do
        rel="${f#$docs/}"

        # Skip SUMMARY.md
        [ "$rel" = "SUMMARY.md" ] && continue

        # Skip files under the build output directory
        case "$f" in "$build_dir"/*) continue ;; esac

        # Derive the title from the first H1; fallback to filename
        title="$(grep -m1 '^# ' "$f" | sed 's/^# *//' || true)"
        if [ -z "$title" ]; then
            base="$(basename "${f%.*}")"
            title="$(printf '%s\n' "$base" \
                | tr '._-' '   ' \
                | awk '{for(i=1;i<=NF;i++){ $i=toupper(substr($i,1,1)) substr($i,2) }}1')"
        fi

        # Indent two spaces per directory depth
        depth="$(awk -F'/' '{print NF-1}' <<<"$rel")"
        indent="$(printf '%*s' $((depth*2)) '')"

        echo "${indent}- [$title](${rel})" >> "$out"
    done < <(find "$docs" -type f -name '*.md' -not -name 'SUMMARY.md' -not -path "$build_dir/*" | LC_ALL=C sort)

    echo "Wrote $out"

# Build the documentation book
book: summary
    mdbook-mermaid install .
    mv mermaid.min.js mermaid-init.js docs/ 2>/dev/null || true
    mdbook build
    rm -f docs/mermaid-init.js docs/mermaid.min.js

# Serve documentation with live reload
serve: summary
    #!/usr/bin/env bash
    set -euo pipefail

    cleanup() {
        echo "Shutting down..."
        jobs -p | xargs -r kill 2>/dev/null || true
    }
    trap cleanup SIGINT SIGTERM EXIT

    mdbook-mermaid install .
    mv mermaid.min.js mermaid-init.js docs/ 2>/dev/null || true

    # Try ports 3000-3005
    for port in 3000 3001 3002 3003 3004 3005; do
        if ! lsof -i:$port >/dev/null 2>&1; then
            echo "Starting mdbook server on port $port..."
            mdbook serve --port $port --open
            exit 0
        fi
    done

    echo "No available ports in range 3000-3005"
    exit 1

# Check for broken links in documentation
link-check:
    lychee --offline docs/*.md

# Check for broken links including external URLs
link-check-external:
    lychee docs/*.md

# ─────────────────────────────────────────────────────────────────────────────
# CI
# ─────────────────────────────────────────────────────────────────────────────

# Run all CI checks locally (dry run)
ci-dry-run: check-launcher build test book link-check
    @echo ""
    @echo "✓ All CI checks passed"
