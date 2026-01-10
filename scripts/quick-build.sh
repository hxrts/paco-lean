#!/usr/bin/env bash
set -euo pipefail

# Quick build for core paco modules.
lake build Paco.Basic Paco.UpTo.Compat Paco.UpTo.Closures Paco.Companion
