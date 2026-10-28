"""Every warrant locator names a statement the source actually numbers.

A warrant says a declaration formalises a named statement of a named work. The
name is checkable: the transcribed source either numbers that statement or it
does not. Nothing here reads the mathematics; it asks only whether the thing
cited exists.

It was written after two failures of that kind on 2026-09-10. The manuscript
cited a theorem one past the last its section numbers. A docstring reported a
regularity theorem as running over `a ∈ W^{k+2,∞}` where the theorem asks
`W^{k+1,∞}`, and that misreading reached the manuscript, because it was taken
from the docstring and not from the source.

The transcriptions live in the local Adduce library, one JSONL of OCR blocks per
work, so this runs offline and needs no key.

    uv run python verify/locator_audit.py [--source gilbarg-2001] [--verbose]
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "proofsense" / "manifest.json"
OCR = Path.home() / ".adduce" / "library" / "ocr"
PDFS = Path.home() / ".adduce" / "library" / "pdfs"

# The manifest names a work by a short id; the library names it by its citation
# key. Anything absent here is reported rather than skipped, so a source added
# to the manifest cannot slip past unchecked.
SOURCE_KEYS: dict[str, str] = {
    "evans-2010": "evans-2010-par-dif-equ",
    "gilbarg-2001": "gilbarg-2001-ell-par-dif",
    "fernandezreal-2023-reg-the-ell": "fernandezreal-2023-reg-the-ell",
    "brezis-2011": "brezis-2011-fun-ana-sob",
}

# A locator names its statement last: `§6.2.3 Thm 4` ends in `4`, `§8.1 Thm
# 8.1` ends in `8.1`. The kind word before it says what to look for.
_KIND = r"Thm|Theorem|Lem|Lemma|Cor|Corollary|Def|Definition|Rmk|Remark|Prop|Proposition|Ex|Example"
_LOCATOR_RE = re.compile(
    rf"(?P<kind>{_KIND})\s*\.?\s*(?P<num>[0-9IVXivx]+(?:\.[0-9]+)*)\s*$",
    re.IGNORECASE,
)

# Some works number nothing at the point a warrant needs, and the locator names
# the statement in words instead. These are read by a person, not by this.
_UNNUMBERED_RE = re.compile(r"\(([^)]+)\)\s*$")

_KIND_WORD = {
    "thm": "theorem", "theorem": "theorem",
    "lem": "lemma", "lemma": "lemma",
    "cor": "corollary", "corollary": "corollary",
    "def": "definition", "definition": "definition",
    "rmk": "remark", "remark": "remark",
    "prop": "proposition", "proposition": "proposition",
    "ex": "example", "example": "example",
}


def _transcription(key: str) -> str | None:
    """The source as text: the OCR blocks and the PDF text layer together.

    Neither alone is enough. The OCR reads the mathematics and drops the odd
    heading, which on a first run here reported four statements as absent
    when all four sit in the PDF, and a check that cries wolf is worse than no
    check. The PDF layer reads headings and mangles display equations. Only
    existence of a numbered statement is asked here, so the union answers it and
    the disagreement between them does not matter.
    """
    parts: list[str] = []
    path = OCR / f"{key}.jsonl"
    if path.exists():
        for line in path.open(encoding="utf-8"):
            record = json.loads(line)
            if not isinstance(record, dict) or "blocks" not in record:
                continue
            for block in record["blocks"]:
                parts.append(block.get("text") or block.get("latex") or "")
    pdf = PDFS / f"{key}.pdf"
    if pdf.exists():
        import subprocess
        try:
            out = subprocess.run(["pdftotext", "-layout", str(pdf), "-"],
                                 capture_output=True, text=True, timeout=300)
            if out.returncode == 0:
                parts.append(out.stdout)
        except (OSError, subprocess.TimeoutExpired):
            pass
    return "\n".join(parts) if parts else None


def _numbering_style(text: str, kind: str) -> bool:
    """Whether the work numbers statements of this kind at all."""
    return re.search(rf"\b{kind}\s+[0-9IVX]", text, re.IGNORECASE) is not None


# The section part of a locator. Where a work numbers within a section, a
# statement must be found inside that section: Evans has forty `THEOREM 1`s, and
# six warrants cited `§5.2.1 Thm 1` where §5.2.1 numbers no theorem at all and
# the statement they meant is `§5.2.3 Thm 1`. Asking the book as a whole passed
# all six.
_SECTION_RE = re.compile(r"§\s*([0-9]+(?:\.[0-9]+)*)")


def _section_slice(text: str, section: str) -> str | None:
    """The text of one numbered section, or nothing when it is not found.

    The table of contents matches the heading too and comes first, so the body
    heading is the last match.
    """
    heads = list(re.finditer(rf"(?m)^\s*{re.escape(section)}\.?\s+[A-Z(]", text))
    if not heads:
        return None
    begin = heads[-1].start()
    nxt = re.compile(r"(?m)^\s*[0-9]+\.[0-9]+(?:\.[0-9]+)?\.?\s+[A-Z]")
    after = [m for m in nxt.finditer(text, begin + 1)
             if not m.group(0).strip().startswith(section)]
    return text[begin: after[0].start()] if after else text[begin:]


def _states(text: str, kind: str, num: str) -> bool:
    """Whether the source numbers a statement of that kind at that number.

    Evans writes `THEOREM 4` under a section heading and Gilbarg and Trudinger
    write `Theorem 8.1` in full, so the section part of a locator is dropped and the
    statement number matched on its own. A number that appears only in a cross
    reference still counts: the work numbers it either way.
    """
    escaped = re.escape(num)
    if re.search(rf"\b{kind}\s*\.?\s*{escaped}\b", text, re.IGNORECASE):
        return True
    # Evans numbers within a section, so `§6.2.3 Thm 4` is `THEOREM 4` there.
    tail = num.split(".")[-1]
    if tail != num and re.search(rf"\b{kind}\s*\.?\s*{re.escape(tail)}\b",
                                 text, re.IGNORECASE):
        return True
    return False


# A citation inside a Lean docstring: `Evans, *Title* (...), Theorem 2`. Any
# author is matched, so a citation of a work with no transcription is reported
# and never passes unread.
# The warrants are one record of what the library leans on and the docstrings
# are another, and a statement cited in one and absent from the source is the
# same defect wherever it sits.
# The stretch between the title and the statement takes an edition, a year and a
# section, `(2nd ed.), §6.3.1,`, and may wrap onto the next docstring line. The
# author pattern is case-sensitive and skips a lowercase word before an italic.
_DOCSTRING_CITE_RE = re.compile(
    r"(?P<author>[A-Z][\w-]+(?:\s+(?:and|&)\s+[A-Z][\w-]+)?)\s*,\s*\*[^*\n]+\*"
    r"(?P<gap>(?:[^*\n]|\n[ \t]*(?=\S)){0,80}?)"
    r"(?P<kind>(?i:Theorem|Thm|Lemma|Corollary|Proposition|Remark|Definition))\s*"
    r"(?P<num>[0-9IVX]+(?:\.[0-9]+)*)",
)

_AUTHOR_SOURCE = {"evans": "evans-2010", "gilbarg": "gilbarg-2001", "trudinger": "gilbarg-2001",
                  "brezis": "brezis-2011",
                  "fernández": "fernandezreal-2023-reg-the-ell",
                  "fernandez": "fernandezreal-2023-reg-the-ell"}


def _docstring_citations() -> list[tuple[str, str, str, str, str | None]]:
    """Every `(source_id, kind, number, file, section)` a Lean docstring cites.

    An author with no source id comes back as `unknown:<author>`."""
    lean = ROOT / "lean" / "EllipticPdes"
    if not lean.is_dir():
        return []
    out: list[tuple[str, str, str, str, str | None]] = []
    for path in sorted(lean.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        for m in _DOCSTRING_CITE_RE.finditer(text):
            author = re.split(r"[\s-]", m.group("author"))[0].lower()
            src = _AUTHOR_SOURCE.get(author, f"unknown:{m.group('author')}")
            secs = _SECTION_RE.findall(m.group("gap"))
            sec = secs[-1] if secs else None
            out.append((src, _KIND_WORD[m.group("kind").lower()], m.group("num"),
                        str(path.relative_to(ROOT)), sec))
    return out


def audit(only: str | None = None) -> list[str]:
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    texts: dict[str, str | None] = {}
    findings: list[str] = []
    seen: set[tuple[str, str]] = set()
    for w in manifest["warrants"]:
        src, loc = w["source_id"], w["locator"]
        if only and src != only:
            continue
        if (src, loc) in seen:
            continue
        seen.add((src, loc))
        key = SOURCE_KEYS.get(src)
        if key is None:
            findings.append(f"{src}: no transcription is mapped for this source")
            continue
        if src not in texts:
            texts[src] = _transcription(key)
        text = texts[src]
        if text is None:
            findings.append(
                f"{src}: no transcription at {OCR / (key + '.jsonl')}; "
                f"run `adduce cite ocr {key}`")
            continue
        m = _LOCATOR_RE.search(loc)
        if m is None:
            if _UNNUMBERED_RE.search(loc):
                continue  # names a statement in words; a person reads it
            findings.append(f"{src} [{loc}]: the locator names no statement")
            continue
        kind = _KIND_WORD[m.group("kind").lower()]
        num = m.group("num")
        if not _numbering_style(text, kind):
            continue  # the work numbers nothing of this kind
        # A bare number is section-local, so Evans's `§5.2.3 Thm 1` has to be
        # found in §5.2.3 and the book's other forty `THEOREM 1`s do not answer
        # for it. A dotted number already names its chapter, as Gilbarg and
        # Trudinger's `8.3` does, and Gilbarg and Trudinger number
        # across a whole chapter, so `Thm 8.3` need not sit in §8.2.
        scope, where = text, "the transcribed source"
        sec = _SECTION_RE.search(loc)
        if sec and "." not in num:
            sliced = _section_slice(text, sec.group(1))
            if sliced:
                scope, where = sliced, f"section {sec.group(1)}"
        if not _states(scope, kind, num):
            decls = sorted({
                x["decl"].split(".")[-1] for x in manifest["warrants"]
                if x["source_id"] == src and x["locator"] == loc
            })
            findings.append(
                f"{src} [{loc}]: no {kind} {num} in {where} "
                f"({', '.join(decls[:3])})")

    # The same question of the docstrings, which cite the literature directly.
    seen_doc: set[tuple[str, str, str, str | None]] = set()
    for src, kind, num, where, section in _docstring_citations():
        if only and src != only:
            continue
        if (src, kind, num, section) in seen_doc:
            continue
        seen_doc.add((src, kind, num, section))
        if src.startswith("unknown:"):
            findings.append(f"{where}: the docstring cites {src[8:]}, an unknown source")
            continue
        key = SOURCE_KEYS.get(src)
        if key is None:
            continue
        if src not in texts:
            texts[src] = _transcription(key)
        text = texts[src]
        if text is None or not _numbering_style(text, kind):
            continue
        # A bare number is section-local here as in a warrant locator.
        scope = text
        if section and "." not in num:
            scope = _section_slice(text, section) or text
        if not _states(scope, kind, num):
            at = f" in section {section}" if section and "." not in num else ""
            findings.append(
                f"{where}: the docstring cites {kind} {num}{at} of {src}, "
                f"which the source does not number")
    return findings


def main(argv: list[str]) -> int:
    only = None
    verbose = "--verbose" in argv
    if "--source" in argv:
        only = argv[argv.index("--source") + 1]
    findings = audit(only)
    total = len({(w["source_id"], w["locator"])
                 for w in json.loads(MANIFEST.read_text(encoding="utf-8"))["warrants"]
                 if not only or w["source_id"] == only})
    for f in findings:
        print(f"  {f}")
    if findings:
        print(f"\n{len(findings)} of {total} locators name nothing in their source.")
        return 1
    if verbose:
        print(f"  checked {total} warrant locators and "
              f"{len({(a, b, c, e) for a, b, c, _, e in _docstring_citations()})} "
              f"docstring citations")
    print("locators: every citation names a statement its source numbers.")
    print("         (existence only; what a statement says is read by a person)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
