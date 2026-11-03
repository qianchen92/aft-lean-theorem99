#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
python3 scripts/verify-snapshot.py
lake build Theorem99
lake env lean Audit.lean
git diff --check
git diff --cached --check
