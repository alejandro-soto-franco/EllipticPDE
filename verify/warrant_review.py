"""Put every warrant beside the statement it cites, and check what is decidable.

A warrant says a declaration formalises a named statement of a named work. Three
things can go wrong, and they need different treatment.

Whether the cited statement exists is decidable, and `locator_audit.py` settles
it. Whether the claim is faithful to the mathematics is a reading, and no
program does that. Between them sits a band that is decidable and was where
every defect of 2026-09-10 lived:

* ``clauses_are_named``
  The cited statement enumerates clauses and the claim is silent about which it
  covers. A claim saying "in full", "the three clauses at once" or "the local
  half" has said it without naming a marker, and counts. Evans §6.2.2
  Theorem 2 states boundedness and the Garding inequality; `garding` gives the
  second alone, and its claim said only "formalises". Six of the ten warrants
  read that day were partial in this way.

* ``named_clauses_exist``
  The claim names a clause the cited statement does not enumerate. Reported for
  reading rather than failing: clause markers survive transcription unevenly,
  and Evans's clause (ii) of §5.6.3 Theorem 6 is in the book and absent from the
  transcription of it.

* ``hypotheses_are_accounted_for``
  A hypothesis the cited statement carries in its own words, absent from both
  the Lean signature and the claim. `interior_H2_estimate` takes the solution in
  `H_0^1` where Evans asks `H^1`, and its claim said nothing. This one is a
  heuristic over notation, so it reports for reading rather than failing.

The point of the packets is that a reading is what settles the rest, and a
reading needs the two texts side by side. ``--packets <dir>`` writes one file per
warrant: the source statement as transcribed, the Lean signature, and the claim.

    uv run python verify/warrant_review.py [--packets out/] [--source guo-2026]
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "proofsense" / "manifest.json"
OCR = Path.home() / ".adduce" / "library" / "ocr"
PDFS = Path.home() / ".adduce" / "library" / "pdfs"

SOURCE_KEYS = {
    "evans-2010": "evans-2010-par-dif-equ",
    "guo-2026": "guo-2026-par-dif-equ",
    "gilbarg-2001": "gilbarg-2001-ell-par-dif",
    "fernandezreal-2023-reg-the-ell": "fernandezreal-2023-reg-the-ell",
}

_KIND = (r"Thm|Theorem|Lem|Lemma|Cor|Corollary|Def|Definition|Rmk|Remark"
         r"|Prop|Proposition|Ex|Example")
_LOCATOR_RE = re.compile(
    rf"(?P<kind>{_KIND})\s*\.?\s*(?P<num>[0-9IVXivx]+(?:\.[0-9]+)*)\s*$", re.IGNORECASE)

# A clause marker as the three works write them: `(i)`, `(ii)`, and the Greek
# pair Evans uses for the Fredholm dichotomy.
_CLAUSE_RE = re.compile(r"\((?:i{1,3}|iv|v|vi{0,3}|[αβ]|a|b|c)\)")
# The bare-parenthesis form is lowercase only. These works write clause markers
# in lowercase roman, and a claim naming a set `W^{k,p}(V)` was read as clause
# (v) when the alternative was case-insensitive.
_CLAUSE_IN_CLAIM_RE = re.compile(
    r"(?:\bclause(?:s)?\s*\(?(?P<named>[ivx]+|[αβ])\)?)|\((?P<bare>i{1,3}|iv|vi{0,3})\)")

# A claim may say what it covers without naming a marker: "in full", "the three
# clauses at once", "without its support clause", "the local half". The check is
# for a claim silent about scope, so these count as having said it.
_SCOPE_RE = re.compile(
    r"\bin full\b|\bclauses\b|\bat once\b|\bboth\b|\bhalf\b|\bwithout its\b"
    r"|\bas (?:Evans|Guo|the source|the cited)\b|\bevery clause\b",
    re.IGNORECASE)

# Hypotheses worth noticing when a statement names one and nothing else does.
# Each is a shape a reader would check, written as the sources write it.
_HYPOTHESIS_TOKENS: tuple[tuple[str, str], ...] = (
    (r"C\s*\^?\s*\{?\s*1\s*\}?\s*(?:boundary|\\partial)", "C^1 boundary"),
    (r"H\s*\^?\s*\{?\s*1\s*\}?\s*\(|H\^\{1\}", "H^1 (not H_0^1)"),
    (r"H\s*_?\s*\{?\s*0\s*\}?\s*\^?\s*\{?\s*1", "H_0^1"),
    (r"L\s*\^?\s*\{?\s*\\infty\s*\}?", "L^infinity"),
    (r"\bbounded\b", "bounded"),
    (r"\bconnected\b", "connected"),
    (r"\bsymmetric\b", "symmetric"),
)


def _source_text(key: str) -> list[tuple[int, str]]:
    """The source as (page, block) pairs, OCR blocks first, PDF pages after."""
    out: list[tuple[int, str]] = []
    path = OCR / f"{key}.jsonl"
    if path.exists():
        for line in path.open(encoding="utf-8"):
            record = json.loads(line)
            if not isinstance(record, dict) or "blocks" not in record:
                continue
            for block in record["blocks"]:
                out.append((record["page"], block.get("text") or block.get("latex") or ""))
    if out:
        return out
    pdf = PDFS / f"{key}.pdf"
    if pdf.exists():
        try:
            res = subprocess.run(["pdftotext", "-layout", str(pdf), "-"],
                                 capture_output=True, text=True, timeout=300)
            if res.returncode == 0:
                out = [(0, line) for line in res.stdout.split("\n")]
        except (OSError, subprocess.TimeoutExpired):
            pass
    return out


_KIND_ALTS = {
    "thm": r"Theorem|Thm", "theorem": r"Theorem|Thm",
    "lem": r"Lemma|Lem", "lemma": r"Lemma|Lem",
    "cor": r"Corollary|Cor", "corollary": r"Corollary|Cor",
    "def": r"Definition|Def", "definition": r"Definition|Def",
    "rmk": r"Remark|Rmk", "remark": r"Remark|Rmk",
    "prop": r"Proposition|Prop", "proposition": r"Proposition|Prop",
    "ex": r"Example|Ex", "example": r"Example|Ex",
}

# The section part of a locator, which Evans needs and Guo does not. Evans
# numbers a theorem within its section, so `§5.2.1 Thm 1` is `THEOREM 1` under
# the heading `5.2.1`, and the book has forty other `THEOREM 1`s.
_SECTION_RE = re.compile(r"§\s*([0-9]+(?:\.[0-9]+)*)")


def statement(blocks: list[tuple[int, str]], kind: str, num: str,
              section: str | None = None) -> str:
    """The cited statement, from its heading to whatever ends it.

    A locator writes `Thm` where the source writes `THEOREM`, so the kind is
    matched on both spellings. The heading has to open a block, or a sentence
    mentioning the statement in passing is taken for the statement itself, which
    is what Gilbarg and Trudinger's cross references do. Where the source
    numbers within a section, the search starts at that section's heading.
    What ends the statement is the proof or the next numbered heading. The
    window is wide because a truncated statement reads as one with fewer
    clauses, and a check that reports a missing clause where the text has it is
    worse than no check.
    """
    alts = _KIND_ALTS.get(kind.lower(), re.escape(kind))
    tail = num.split(".")[-1]
    head = re.compile(
        rf"^\s*(?:{alts})\s*\.?\s*(?:{re.escape(num)}|{re.escape(tail)})\b",
        re.IGNORECASE)
    begin, end = 0, len(blocks)
    if section:
        sec = re.compile(rf"^\s*{re.escape(section)}\.?\s+[A-Z(]")
        # The table of contents matches the heading too and comes first, so the
        # body heading is the last match. Taking the first sent `§5.7 Thm 1` to
        # the first `THEOREM 1` after the contents page, which is §5.1's.
        at = [i for i, (_, t) in enumerate(blocks) if sec.match(t)]
        if at:
            begin = at[-1]
            # Stop at the next section heading, so a statement the section does
            # not contain is reported missing instead of matching a later one.
            nxt = re.compile(r"^\s*[0-9]+\.[0-9]+(?:\.[0-9]+)?\.?\s+[A-Z]")
            after = [i for i, (_, t) in enumerate(blocks[begin + 1:], begin + 1)
                     if nxt.match(t) and not t.strip().startswith(section)]
            if after:
                end = after[0]
    start = next((i for i, (_, t) in enumerate(blocks[begin:end], begin)
                  if head.match(t)), None)
    if start is None:
        return ""
    stop = re.compile(
        rf"^\s*(?:Proof\b|Remarks?\b|(?:{_KIND})\s*\.?\s*[0-9IVX])", re.IGNORECASE)
    parts = [blocks[start][1]]
    for _, t in blocks[start + 1: start + 40]:
        if stop.match(t):
            break
        parts.append(t)
    return "\n".join(parts)


_DECL_HEAD_RE = re.compile(
    r"^(?:@\[.*?\]\s*)?(?:private\s+|protected\s+)?(?:noncomputable\s+)?"
    r"(?:theorem|lemma|def|instance|abbrev)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)",
    re.MULTILINE)


def _lean_signatures() -> dict[str, str]:
    """Every declaration's Lean signature, by unqualified name.

    Parsed here rather than imported from the manuscript's transcriber, which
    lives in the other repository. This needs the header text alone, and a
    dependency between the two repositories to get it would be the wrong trade.
    """
    root = ROOT / "lean" / "EllipticPdes"
    if not root.is_dir():
        return {}
    sigs: dict[str, str] = {}
    for path in sorted(root.rglob("*.lean")):
        lines = path.read_text(encoding="utf-8").split("\n")
        for i, line in enumerate(lines):
            m = _DECL_HEAD_RE.match(line)
            if not m:
                continue
            body = [line]
            for nxt in lines[i + 1: i + 40]:
                body.append(nxt)
                if re.search(r":=|\bby\b\s*$", nxt):
                    break
            sigs[m.group("name").split(".")[-1]] = "\n".join(body)
    return sigs


def review(only: str | None = None) -> tuple[list[str], list[str]]:
    """Returns (failures, readings): what is decidable, and what a person reads."""
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    sigs = _lean_signatures()
    texts: dict[str, list[tuple[int, str]]] = {}
    failures: list[str] = []
    readings: list[str] = []
    # A divergence between a cited statement and the family of declarations
    # warranted against it, recorded once rather than repeated in every claim.
    # A reading it names is settled; anything else still reports.
    recorded: dict[tuple[str, str], set[str]] = {}
    for dv in manifest.get("source_divergences", []):
        recorded.setdefault((dv["source_id"], dv["locator"]), set()).update(dv["labels"])
    for w in manifest["warrants"]:
        src, loc, decl, claim = w["source_id"], w["locator"], w["decl"], w["claim"]
        if only and src != only:
            continue
        key = SOURCE_KEYS.get(src)
        if key is None:
            continue
        if src not in texts:
            texts[src] = _source_text(key)
        m = _LOCATOR_RE.search(loc)
        if m is None:
            continue
        sec = _SECTION_RE.search(loc)
        body = statement(texts[src], m.group("kind"), m.group("num"),
                         sec.group(1) if sec else None)
        if not body:
            continue
        short = decl.split(".")[-1]

        clauses = {c.lower() for c in _CLAUSE_RE.findall(body)}
        # `(a)`, `(b)`, `(c)` appear in ordinary prose, so a statement counts as
        # enumerated only on the roman or Greek markers.
        enumerated = {c for c in clauses if c not in {"(a)", "(b)", "(c)"}}
        named = {g.lower() for pair in _CLAIN(claim) for g in pair if g}

        if len(enumerated) >= 2 and not named and not _SCOPE_RE.search(claim):
            failures.append(
                f"{short} against {src} [{loc}]: the statement enumerates "
                f"{', '.join(sorted(enumerated))} and the claim names no clause")
        for n in named:
            marker = f"({n})"
            if enumerated and marker not in enumerated:
                # A reading, not a failure. Evans's clause (ii) of §5.6.3
                # Theorem 6 is in the book and absent from the transcription, so
                # a missing marker says as much about the OCR as about the
                # claim, and no build should rest on this direction.
                readings.append(
                    f"{short} against {src} [{loc}]: the claim names clause {marker}, "
                    f"and the transcribed statement enumerates only "
                    f"{', '.join(sorted(enumerated))}")

        sig = sigs.get(short, "")
        for pattern, label in _HYPOTHESIS_TOKENS:
            if not re.search(pattern, body, re.IGNORECASE):
                continue
            if re.search(pattern, sig, re.IGNORECASE) or label.lower() in claim.lower():
                continue
            if label in recorded.get((src, loc), ()):
                continue
            readings.append(
                f"{short} against {src} [{loc}]: the statement names "
                f"\"{label}\", which neither the signature nor the claim does")
    return failures, readings


def _CLAIN(claim: str) -> list[tuple[str, ...]]:
    return [(m.group("named") or "", m.group("bare") or "")
            for m in _CLAUSE_IN_CLAIM_RE.finditer(claim)]


def write_packets(out_dir: Path, only: str | None = None) -> int:
    """One file per warrant: the source statement, the signature, and the claim."""
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    sigs = _lean_signatures()
    texts: dict[str, list[tuple[int, str]]] = {}
    out_dir.mkdir(parents=True, exist_ok=True)
    written = 0
    for w in manifest["warrants"]:
        src, loc, decl = w["source_id"], w["locator"], w["decl"]
        if only and src != only:
            continue
        key = SOURCE_KEYS.get(src)
        if key is None:
            continue
        if src not in texts:
            texts[src] = _source_text(key)
        m = _LOCATOR_RE.search(loc)
        sec = _SECTION_RE.search(loc)
        body = statement(texts[src], m.group("kind"), m.group("num"),
                         sec.group(1) if sec else None) if m else ""
        short = decl.split(".")[-1]
        name = re.sub(r"[^A-Za-z0-9_.-]+", "-", f"{short}__{src}__{loc}")
        (out_dir / f"{name}.md").write_text(
            f"# {decl}\n\n## Cited\n\n{src} [{loc}]\n\n"
            f"### As the source states it\n\n```\n{body or '(not extracted)'}\n```\n\n"
            f"### As Lean states it\n\n```lean\n{sigs.get(short, '(signature not found)')}\n```\n\n"
            f"### As the warrant claims it\n\n{w['claim']}\n",
            encoding="utf-8")
        written += 1
    return written


def main(argv: list[str]) -> int:
    only = argv[argv.index("--source") + 1] if "--source" in argv else None
    if "--packets" in argv:
        out = Path(argv[argv.index("--packets") + 1])
        n = write_packets(out, only)
        print(f"warrant review: {n} packets written to {out}")
        return 0
    failures, readings = review(only)
    for f in failures:
        print(f"  {f}")
    if readings and "--quiet" not in argv:
        print(f"\n  {len(readings)} hypothesis(es) to read:")
        for r in readings[:40]:
            print(f"    {r}")
        if len(readings) > 40:
            print(f"    ... and {len(readings) - 40} more")
    if failures:
        print(f"\n{len(failures)} warrant(s) name no clause of a statement that has them.")
        return 1
    print("\nwarrant review: every enumerated statement has its clause named.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
