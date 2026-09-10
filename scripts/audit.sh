#!/usr/bin/env bash
# Checks that need the local Adduce library, which a CI runner does not have.
#
# `verify/locator_audit.py` asks whether every statement the warrants and the
# docstrings cite is one the source numbers. `verify/warrant_review.py` puts each
# warrant beside the statement it cites and checks what is decidable of the two,
# and prints what a person still has to read. Both read the transcribed sources,
# which are copyrighted and local, so they run here and CI runs their tests.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 1

FAILED=0
run() {
    printf '\n\033[1m==> %s\033[0m\n' "$1"; shift
    "$@" || FAILED=1
}

run "warrant coverage" uv run python verify/proofsense_coverage.py
run "locator audit" uv run python verify/locator_audit.py --verbose
run "warrant content review" uv run python verify/warrant_review.py
run "verify tests" uv run --with pytest python -m pytest verify/ -q

printf '\n'
[ "$FAILED" -eq 0 ] && { printf 'audit: clean.\n'; exit 0; }
printf 'audit: findings above.\n'; exit 1
