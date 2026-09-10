#!/usr/bin/env bash
# Checks that need the local Adduce library, which a CI runner does not have.
#
# `verify/locator_audit.py` reads the transcribed sources to ask whether every
# statement the warrants and the docstrings cite is one the source numbers. The
# transcriptions are copyrighted and local, so this runs here and CI runs the
# audit's own tests instead.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 1

FAILED=0
run() {
    printf '\n\033[1m==> %s\033[0m\n' "$1"; shift
    "$@" || FAILED=1
}

run "warrant coverage" uv run python verify/proofsense_coverage.py
run "locator audit" uv run python verify/locator_audit.py --verbose
run "verify tests" uv run --with pytest python -m pytest verify/ -q

printf '\n'
[ "$FAILED" -eq 0 ] && { printf 'audit: clean.\n'; exit 0; }
printf 'audit: findings above.\n'; exit 1
