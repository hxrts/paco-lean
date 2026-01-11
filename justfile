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
ci-dry-run: build test book link-check
    @echo ""
    @echo "✓ All CI checks passed"
