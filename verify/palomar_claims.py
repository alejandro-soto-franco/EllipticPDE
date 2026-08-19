#!/usr/bin/env python3
"""
Bind the prose of a Palomar submission to the statements it describes.

The 2026-08-19 review of this repository returned five blocking problems, every one a
sentence that the Lean did not support. The instructive one had been true when it was
written: `fidelity.divergences` said compactness of the embedding is a hypothesis, which it
was until the statements moved to a bounded measurable domain, and nothing noticed the
sentence going stale. A build cannot catch that, and neither can a linter that reads prose
alone.

So each compared declaration carries the digest of its own elaborated type in
`lean/palomar-claims.lock.json`. Change a statement and the digest moves, the lock goes
stale, and this refuses to pass until someone re-reads the prose and signs it again. That
is the whole point: signing asserts a human compared the sentence with the type.

Seven rules run alongside the lock, each one a defect a review actually found. The last
three come from the second review, and the first of those is the reason the corpus below
is read from every prose field rather than from `project.description`: the stale sentence
that survived the first round sat in `status.scope`, which nothing was reading.

  * every compared declaration has an `alignment.statements` row, and every row names a
    compared declaration, so the described set and the selected set cannot drift apart;
  * the metadata may not describe compactness as a hypothesis while no compared statement
    takes one;
  * a statement written in the shifted form `B[u, v] = μ ⟨u, v⟩ + ⟨f, v⟩` must be
    described as `L u = μ u + f`, never with the opposite sign;
  * the scope paragraph must state how many declarations the configuration selects, and
    the number must be right;
  * no prose may say the submission covers one result alone while the configuration
    selects several;
  * a constant that a statement supplies as a structure field may not be described as a
    norm of the coefficient it bounds, since a caller may hand over a loose bound;
  * prose may not describe the compared statements as asking for a measurable domain when
    they ask for an open one.

Run:  uv run --with pyyaml python verify/palomar_claims.py
      uv run --with pyyaml python verify/palomar_claims.py --sign   (after re-reading)
Exit code 0 iff every rule passes and the lock is current.
"""

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PROJECT = ROOT / "lean"
CONFIG = PROJECT / "comparator.json"
META = PROJECT / "formalization.yaml"
LOCK = PROJECT / "palomar-claims.lock.json"

NUMBER_WORDS = {1: "one", 2: "two", 3: "three", 4: "four", 5: "five", 6: "six",
                7: "seven", 8: "eight", 9: "nine", 10: "ten", 11: "eleven", 12: "twelve"}

# Prose that asserts the compact embedding is assumed rather than derived. A sentence
# denying the claim, "compactness is derived, not assumed", uses the same words, so the
# rule reads one sentence at a time and a denial clears it.
COMPACTNESS_CLAIMED = re.compile(
    r"compact\w*[^.]{0,90}?(is a hypothesis|as a hypothesis|is assumed|are assumed"
    r"|enters as a hypothesis)", re.I)
COMPACTNESS_DENIED = re.compile(
    r"\bno\b|\bnot\b|never|rather than|derived|discharged|proved|does not", re.I)
# The shifted problem, written with the sign the Lean does not use.
WRONG_SHIFT_SIGN = re.compile(r"L\s*u\s*\+\s*[μλ]\s*u\s*=\s*f")
RIGHT_SHIFT_SIGN = re.compile(r"L\s*u\s*=\s*[μλ]\s*u\s*\+\s*f")
# Prose that reduces the submission to a single result. Both forms below stood in the
# metadata for a widened configuration, one in `status.scope` and one in a YAML comment.
SINGLE_RESULT = re.compile(
    r"(this submission|configuration|comparator)[^.]{0,90}\balone\b"
    r"|\bonly the [^.]{0,70}(carries|has) a comparator", re.I)
# A norm written where the statement takes a supplied bound.
SUPREMUM_NORM = re.compile(r"‖\s*[bc]\s*‖\s*_?[∞_]|essential supremum of\s*[bc]\b", re.I)
# Prose that attributes a domain hypothesis to the compared statements. The library states
# its own theory for a measurable domain and must not trip the rule. Hence the subject
# phrase has to precede the word.
MEASURABLE_DOMAIN = re.compile(
    r"(compared statement|formal statement|statement here|statements below|this submission)"
    r"[^.]{0,160}\bmeasurable\b(?!\s+coefficient)", re.I)

results: list[tuple[bool, str, str]] = []


def check(ok: bool, name: str, detail: str = "") -> None:
    results.append((ok, name, detail))


def statement_types(names: list[str]) -> dict[str, str]:
    """The elaborated type of each compared declaration, as Lean prints it."""
    probe = PROJECT / "PalomarClaimsProbe.lean"
    body = ["import Challenge", "set_option pp.fullNames true"]
    body += [f"#check @{name}" for name in names]
    probe.write_text("\n".join(body) + "\n", encoding="utf-8")
    try:
        # The probe imports the built module, so an edited but unbuilt `Challenge.lean`
        # would be read at its previous types and the lock would pass on stale digests.
        subprocess.run(["lake", "build", "Challenge"], cwd=PROJECT, capture_output=True)
        out = subprocess.run(["lake", "env", "lean", probe.name], cwd=PROJECT,
                             capture_output=True, text=True).stdout
    finally:
        probe.unlink(missing_ok=True)
    # Each `#check` block opens on `@Name :`.
    blocks = re.split(r"(?m)^(?=@)", out)
    types: dict[str, str] = {}
    for block in blocks:
        m = re.match(r"@(\S+)\s*:", block)
        if m and m[1] in names:
            types[m[1]] = " ".join(block.split())
    return types


def docstrings() -> dict[str, str]:
    """The docstring attached to each theorem in Challenge.lean."""
    source = (PROJECT / "Challenge.lean").read_text(encoding="utf-8")
    found: dict[str, str] = {}
    for m in re.finditer(r"/--(.*?)-/\s*theorem\s+(\w+)", source, re.S):
        found[m[2]] = " ".join(m[1].split())
    return found


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sign", action="store_true",
                        help="record the current statements and prose as read")
    args = parser.parse_args()

    import yaml

    config = json.loads(CONFIG.read_text(encoding="utf-8"))
    names = config["theorem_names"]
    meta = yaml.safe_load(META.read_text(encoding="utf-8"))
    types = statement_types(names)
    docs = docstrings()

    missing = [n for n in names if n not in types]
    check(not missing, "every compared declaration elaborates", ", ".join(missing))
    if missing:
        return report()

    # 1. the described set and the selected set agree
    rows = meta.get("alignment", {}).get("statements", [])
    described = {r.get("lean") for r in rows}
    check(set(names) <= described, "every compared declaration has an alignment row",
          ", ".join(sorted(set(names) - described)))
    check(described <= set(names), "every alignment row names a compared declaration",
          ", ".join(sorted(described - set(names))))

    # 2. compactness is not described as a hypothesis when no statement takes one
    takes_compactness = [n for n, t in types.items() if "IsCompactOperator" in t]
    prose = "\n".join([
        meta.get("fidelity", {}).get("divergences", ""),
        meta.get("project", {}).get("description", ""),
        meta.get("status", {}).get("scope", ""),
        # the YAML parser strips comments; the file itself is read for them
        *[line.lstrip("# ").strip() for line in META.read_text(encoding="utf-8").splitlines()
          if line.lstrip().startswith("#")],
        *[r.get("note", "") for r in rows],
        *docs.values(),
    ])
    sentences = [x.strip() for x in re.split(r"(?<=[.;])\s+", prose)]
    offending = [x for x in sentences if COMPACTNESS_CLAIMED.search(x)
                 and not COMPACTNESS_DENIED.search(x)]
    check(bool(takes_compactness) or not offending,
          "no prose calls compactness a hypothesis while no statement takes one",
          offending[0][:90] if offending else "")

    # 3. the shifted problem is described with the sign the Lean uses
    for name, typ in types.items():
        short = name.rsplit(".", 1)[-1]
        text = docs.get(short, "") + " " + " ".join(
            r.get("note", "") for r in rows if r.get("lean") == name)
        if "zerothPairing" not in typ:
            continue
        wrong = WRONG_SHIFT_SIGN.search(text)
        check(wrong is None, f"{short} is not described with the opposite shift sign",
              wrong.group(0) if wrong else "")
        check(bool(RIGHT_SHIFT_SIGN.search(text)),
              f"{short} states the shifted equation explicitly",
              "" if RIGHT_SHIFT_SIGN.search(text) else "expected L u = μ u + f")

    # 4a. no prose reduces a configuration of several declarations to one result
    single = [x for x in sentences if len(names) > 1 and SINGLE_RESULT.search(x)]
    check(not single, "no prose says the submission covers one result alone",
          single[0][:90] if single else "")

    # 4b. a supplied bound is not described as the norm it bounds
    supplied = {f for n, t in types.items() for f in ("Csup", "Bsup") if f in t}
    norms = [x for x in sentences if SUPREMUM_NORM.search(x)]
    check(not (supplied and norms),
          "no prose calls a supplied coefficient bound an essential supremum",
          norms[0][:90] if norms else "")

    # 4c. the domain hypothesis in the prose is the one the statements take
    opens = any("IsOpen" in t for t in types.values())
    measurables = any("MeasurableSet" in t for t in types.values())
    stale = [x for x in sentences if MEASURABLE_DOMAIN.search(x)]
    check(not (opens and not measurables and stale),
          "the domain hypothesis described is the one the statements take",
          stale[0][:90] if stale else "")

    # 5. the scope paragraph counts the selected declarations
    description = meta.get("project", {}).get("description", "")
    word = NUMBER_WORDS.get(len(names), str(len(names)))
    counted = re.search(rf"selects {word} declarations", description, re.I) is not None
    check(counted, "the description states how many declarations the configuration selects",
          "" if counted else f"expected 'selects {word} declarations'")

    # 6. the lock: a statement or its prose cannot change unread
    current = {name: {"type_sha256": digest(types[name]),
                      "docstring_sha256": digest(docs.get(name.rsplit(".", 1)[-1], ""))}
               for name in names}
    if args.sign:
        LOCK.write_text(json.dumps(current, indent=2, sort_keys=True) + "\n",
                        encoding="utf-8")
        print(f"signed {len(current)} declarations into {LOCK.relative_to(ROOT)}")
        return 0
    if not LOCK.exists():
        check(False, "the claims lock exists", "run with --sign after reading the prose")
        return report()
    locked = json.loads(LOCK.read_text(encoding="utf-8"))
    check(set(locked) == set(current), "the lock covers exactly the compared declarations",
          ", ".join(sorted(set(locked) ^ set(current))))
    for name in sorted(set(locked) & set(current)):
        short = name.rsplit(".", 1)[-1]
        check(locked[name]["type_sha256"] == current[name]["type_sha256"],
              f"{short}: the statement is the one that was read",
              "the type moved; re-read the prose and sign again")
        check(locked[name]["docstring_sha256"] == current[name]["docstring_sha256"],
              f"{short}: the docstring is the one that was read",
              "the docstring moved; re-read it against the type and sign again")
    return report()


def report() -> int:
    width = max(len(name) for _, name, _ in results)
    for ok, name, detail in results:
        print(f"  {'pass' if ok else 'FAIL'}  {name:<{width}}  {detail}")
    failed = [name for ok, name, _ in results if not ok]
    print(f"\n{len(results) - len(failed)}/{len(results)} claim checks pass")
    if failed:
        print("failing: " + ", ".join(failed))
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
