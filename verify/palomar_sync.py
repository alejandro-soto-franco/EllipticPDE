#!/usr/bin/env python3
"""
Hold `lean/Solution.lean` to the definitions of `lean/Challenge.lean`.

Comparator looks a theorem up by name in both modules and compares the two statements,
so `Solution.lean` restates the definitions instead of importing `Challenge.lean`. Two
copies of the same text drift, and drift here does not break the build: it produces two
statements that elaborate, differ, and fail only under Comparator, after submission.

The shared region runs from the first `open MeasureTheory` to the section heading that
introduces the theorem. This compares the two copies character for character and reports
the first line that differs. It also compares the statement of every theorem that
`comparator.json` names, from `theorem <name>` to its `:=`, with whitespace folded.

Run:  uv run python verify/palomar_sync.py
Exit code 0 iff the copies agree.
"""

import difflib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CHALLENGE = ROOT / "lean" / "Challenge.lean"
SOLUTION = ROOT / "lean" / "Solution.lean"

OPEN_MARKER = "open MeasureTheory"
END_MARKER = "/-! ### "


def shared_region(path: Path) -> list[str]:
    """The definition block: from `open MeasureTheory` to the heading after `weakForm`."""
    text = path.read_text(encoding="utf-8")
    start = text.index(OPEN_MARKER)
    end = text.index(END_MARKER, text.index("def weakForm"))
    return text[start:end].rstrip().splitlines(keepends=True)


CONFIG = ROOT / "lean" / "comparator.json"


def statement(text: str, name: str) -> str | None:
    """The statement of theorem `name`: from `theorem <short name>` to its `:=`, whitespace folded."""
    short = name.split(".")[-1]
    m = re.search(rf"^theorem {re.escape(short)}\b(.*?):=", text, flags=re.S | re.M)
    return " ".join(m.group(1).split()) if m else None


def check_statements() -> int:
    """Every compared theorem is stated identically in both modules."""
    names = json.loads(CONFIG.read_text(encoding="utf-8"))["theorem_names"]
    texts = [p.read_text(encoding="utf-8") for p in (CHALLENGE, SOLUTION)]
    bad = 0
    for name in names:
        c, s = (statement(t, name) for t in texts)
        if c is None or s is None:
            print(f"{name}: statement not found in {'Challenge' if c is None else 'Solution'}")
            bad += 1
        elif c != s:
            print(f"{name}: statements differ\n  Challenge: {c}\n  Solution:  {s}")
            bad += 1
    if not bad:
        print(f"{len(names)} compared statements agree")
    return 1 if bad else 0


def main() -> int:
    for path in (CHALLENGE, SOLUTION):
        if not path.exists():
            print(f"missing {path}", file=sys.stderr)
            return 2

    statements_bad = check_statements()
    challenge, solution = shared_region(CHALLENGE), shared_region(SOLUTION)
    if challenge == solution:
        print(f"{len(challenge)} shared lines agree")
        return statements_bad

    diff = difflib.unified_diff(
        challenge, solution, fromfile="Challenge.lean", tofile="Solution.lean", n=1
    )
    print("the shared definitions have drifted:\n")
    sys.stdout.writelines(diff)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
