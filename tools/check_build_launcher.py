#!/usr/bin/env python3
"""Reject project Lake builds that bypass the Paco build launcher."""

from __future__ import annotations

import argparse
from pathlib import Path
import re


def violations(path: Path) -> list[str]:
    result = []
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not re.search(r"\blake\s+build\b", line):
            continue
        if "--no-build" in line:
            continue
        if "{{lean_build}}" not in line:
            result.append(f"{path}:{number}: project lake build bypasses {{lean_build}}")
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("path", nargs="?", type=Path, default=Path("justfile"))
    args = parser.parse_args()
    found = violations(args.path)
    if found:
        print("\n".join(found))
        return 1
    print("build launcher audit: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
