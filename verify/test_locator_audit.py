"""Tests for the locator audit.

A check that has never failed is a check nobody should trust, so each case here
is a citation that should be caught, alongside the real one that should not.
"""

from __future__ import annotations

import json

import pytest

import locator_audit as la


@pytest.fixture
def manifest(tmp_path, monkeypatch):
    """A manifest and a transcription the module is pointed at."""
    (tmp_path / "proofsense").mkdir()
    ocr = tmp_path / "ocr"
    ocr.mkdir()
    (tmp_path / "pdfs").mkdir()
    monkeypatch.setattr(la, "ROOT", tmp_path)
    monkeypatch.setattr(la, "MANIFEST", tmp_path / "proofsense" / "manifest.json")
    monkeypatch.setattr(la, "OCR", ocr)
    monkeypatch.setattr(la, "PDFS", tmp_path / "pdfs")

    def write(warrants: list[dict], source_text: str) -> None:
        (tmp_path / "proofsense" / "manifest.json").write_text(
            json.dumps({"warrants": warrants}), encoding="utf-8")
        (ocr / "gilbarg-2001-ell-par-dif.jsonl").write_text(
            json.dumps({"page": 1, "blocks": [{"text": source_text}]}) + "\n",
            encoding="utf-8")

    return write


def _warrant(locator: str) -> dict:
    return {"decl": "EllipticPdes.t", "source_id": "gilbarg-2001",
            "locator": locator, "claim": "formalises it"}


def test_a_locator_the_source_does_not_number_is_found(manifest):
    """A manuscript once cited a theorem one past the last its section numbers."""
    manifest([_warrant("§6.3 Thm 6.16")],
             "Theorem 6.13. The Dirichlet problem. Theorem 6.15. Fredholm alternative.")
    findings = la.audit()
    assert findings and "6.16" in findings[0]


def test_a_locator_the_source_numbers_passes(manifest):
    manifest([_warrant("§6.3 Thm 6.15")],
             "Theorem 6.15. Fredholm alternative.")
    assert la.audit() == []


def test_a_section_numbered_statement_matches_on_its_own_number(manifest):
    """Evans writes `THEOREM 4` under a heading where a warrant says 6.2.3."""
    manifest([{"decl": "EllipticPdes.t", "source_id": "evans-2010",
               "locator": "§6.2.3 Thm 4", "claim": "formalises it"}],
             "unused")
    (la.OCR / "evans-2010-par-dif-equ.jsonl").write_text(
        json.dumps({"page": 1, "blocks": [{"text": "THEOREM 4 (Fredholm alternative)."}]})
        + "\n", encoding="utf-8")
    assert la.audit() == []


def test_a_source_with_no_transcription_is_reported(manifest, monkeypatch):
    """A missing transcription is reported rather than passed over."""
    manifest([_warrant("§6.3 Thm 6.15")], "Theorem 6.15.")
    (la.OCR / "gilbarg-2001-ell-par-dif.jsonl").unlink()
    findings = la.audit()
    assert findings and "adduce cite ocr" in findings[0]


def test_a_source_the_map_does_not_know_is_reported(manifest):
    manifest([{"decl": "EllipticPdes.t", "source_id": "brand-new-2026",
               "locator": "Thm 1", "claim": "formalises it"}], "Theorem 1.")
    findings = la.audit()
    assert findings and "no transcription is mapped" in findings[0]


def test_a_locator_naming_a_statement_in_words_is_left_to_a_reader(manifest):
    """`App. A (H3)` names a labelled property, which no number resolves."""
    manifest([_warrant("App. A (H3)")], "Theorem 6.15.")
    assert la.audit() == []


def test_a_docstring_citing_a_statement_the_source_lacks_is_found(manifest, tmp_path):
    """The docstrings are a second record of what the library leans on."""
    manifest([], "Theorem 8.3. The generalized Dirichlet problem.")
    lean = tmp_path / "lean" / "EllipticPdes"
    lean.mkdir(parents=True)
    (lean / "A.lean").write_text(
        "/-- Gilbarg and Trudinger, *Elliptic PDE of Second Order* (2001), Theorem 8.99 asks. -/\n"
        "theorem t : True := trivial\n", encoding="utf-8")
    findings = la.audit()
    assert findings and "8.99" in findings[0]


def test_a_docstring_citing_a_statement_the_source_numbers_passes(manifest, tmp_path):
    manifest([], "Theorem 8.3. The generalized Dirichlet problem.")
    lean = tmp_path / "lean" / "EllipticPdes"
    lean.mkdir(parents=True)
    (lean / "A.lean").write_text(
        "/-- Gilbarg and Trudinger, *Elliptic PDE of Second Order* (2001), Theorem 8.3 asks. -/\n"
        "theorem t : True := trivial\n", encoding="utf-8")
    assert la.audit() == []


def test_a_bare_number_must_be_found_in_its_own_section(manifest):
    """Six warrants cited Evans `§5.2.1 Thm 1`, and §5.2.1 numbers no theorem.

    The book has forty other `THEOREM 1`s, so asking it as a whole passed all
    six.
    """
    manifest([{"decl": "EllipticPdes.t", "source_id": "evans-2010",
               "locator": "§5.2.1 Thm 1", "claim": "formalises it"}], "unused")
    (la.OCR / "evans-2010-par-dif-equ.jsonl").write_text(
        json.dumps({"page": 1, "blocks": [
            {"text": "5.2.1. Weak derivatives."},
            {"text": "LEMMA (Uniqueness of weak derivatives)."},
            {"text": "5.2.3. Elementary properties."},
            {"text": "THEOREM 1 (Properties of weak derivatives)."}]}) + "\n",
        encoding="utf-8")
    findings = la.audit()
    assert findings and "section 5.2.1" in findings[0]


def test_a_bare_number_found_in_its_own_section_passes(manifest):
    manifest([{"decl": "EllipticPdes.t", "source_id": "evans-2010",
               "locator": "§5.2.3 Thm 1", "claim": "formalises it"}], "unused")
    (la.OCR / "evans-2010-par-dif-equ.jsonl").write_text(
        json.dumps({"page": 1, "blocks": [
            {"text": "5.2.3. Elementary properties."},
            {"text": "THEOREM 1 (Properties of weak derivatives)."}]}) + "\n",
        encoding="utf-8")
    assert la.audit() == []


def test_a_dotted_number_is_not_confined_to_the_cited_section(manifest):
    """Gilbarg and Trudinger number across a chapter, so `Thm 8.3` may sit
    outside §8.2."""
    manifest([{"decl": "EllipticPdes.t", "source_id": "gilbarg-2001",
               "locator": "§8.2 Thm 8.3", "claim": "formalises it"}], "unused")
    (la.OCR / "gilbarg-2001-ell-par-dif.jsonl").write_text(
        json.dumps({"page": 1, "blocks": [
            {"text": "8.2. SOMETHING ELSE"},
            {"text": "8.4. ANOTHER SECTION"},
            {"text": "Theorem 8.3. The generalized Dirichlet problem."}]}) + "\n",
        encoding="utf-8")
    assert la.audit() == []


def test_unknown_author_citation_is_an_error(manifest, tmp_path):
    """A docstring citing a work the audit has no transcription for is reported."""
    manifest([], "Theorem 8.3. The generalized Dirichlet problem.")
    lean = tmp_path / "lean" / "EllipticPdes"
    lean.mkdir(parents=True)
    (lean / "A.lean").write_text(
        "/-- Kufner, *Weighted Sobolev Spaces* (1985), Theorem 3.4 asks. -/\n"
        "theorem t : True := trivial\n", encoding="utf-8")
    findings = la.audit()
    assert findings and "unknown source" in findings[0]


def test_initialled_gilbarg_trudinger_citation_resolves(manifest, tmp_path):
    """`D. Gilbarg and N. S. Trudinger, *Title*` names Gilbarg and Trudinger."""
    manifest([], "Theorem 8.3. The generalized Dirichlet problem.")
    lean = tmp_path / "lean" / "EllipticPdes"
    lean.mkdir(parents=True)
    (lean / "A.lean").write_text(
        "/-- D. Gilbarg and N. S. Trudinger, *Elliptic PDE of Second Order* (2001), Theorem 8.3. -/\n"
        "theorem t : True := trivial\n", encoding="utf-8")
    assert la.audit() == []
