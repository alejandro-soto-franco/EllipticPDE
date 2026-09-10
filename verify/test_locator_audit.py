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
        (ocr / "guo-2026-par-dif-equ.jsonl").write_text(
            json.dumps({"page": 1, "blocks": [{"text": source_text}]}) + "\n",
            encoding="utf-8")

    return write


def _warrant(locator: str) -> dict:
    return {"decl": "EllipticPdes.t", "source_id": "guo-2026",
            "locator": locator, "claim": "formalises it"}


def test_a_locator_the_source_does_not_number_is_found(manifest):
    """Guo's section VII.4 stops at VII.4.6, and the manuscript cited VII.4.7."""
    manifest([_warrant("§VII.4 Thm VII.4.7")],
             "Theorem VII.4.4. Fredholm Alternative. Remark VII.4.6.")
    findings = la.audit()
    assert findings and "VII.4.7" in findings[0]


def test_a_locator_the_source_numbers_passes(manifest):
    manifest([_warrant("§VII.4 Thm VII.4.4")],
             "Theorem VII.4.4. Fredholm Alternative.")
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
    manifest([_warrant("§VII.4 Thm VII.4.4")], "Theorem VII.4.4.")
    (la.OCR / "guo-2026-par-dif-equ.jsonl").unlink()
    findings = la.audit()
    assert findings and "adduce cite ocr" in findings[0]


def test_a_source_the_map_does_not_know_is_reported(manifest):
    manifest([{"decl": "EllipticPdes.t", "source_id": "brand-new-2026",
               "locator": "Thm 1", "claim": "formalises it"}], "Theorem 1.")
    findings = la.audit()
    assert findings and "no transcription is mapped" in findings[0]


def test_a_locator_naming_a_statement_in_words_is_left_to_a_reader(manifest):
    """`App. A (H3)` names a labelled property, which no number resolves."""
    manifest([_warrant("App. A (H3)")], "Theorem VII.4.4.")
    assert la.audit() == []


def test_a_docstring_citing_a_statement_the_source_lacks_is_found(manifest, tmp_path):
    """The docstrings are a second record of what the library leans on."""
    manifest([], "Theorem VIII.3.2. Higher Interior Regularity.")
    lean = tmp_path / "lean" / "EllipticPdes"
    lean.mkdir(parents=True)
    (lean / "A.lean").write_text(
        "/-- Guo, *Partial Differential Equations* (Notes), Theorem VIII.9.9 asks. -/\n"
        "theorem t : True := trivial\n", encoding="utf-8")
    findings = la.audit()
    assert findings and "VIII.9.9" in findings[0]


def test_a_docstring_citing_a_statement_the_source_numbers_passes(manifest, tmp_path):
    manifest([], "Theorem VIII.3.2. Higher Interior Regularity.")
    lean = tmp_path / "lean" / "EllipticPdes"
    lean.mkdir(parents=True)
    (lean / "A.lean").write_text(
        "/-- Guo, *Partial Differential Equations* (Notes), Theorem VIII.3.2 asks. -/\n"
        "theorem t : True := trivial\n", encoding="utf-8")
    assert la.audit() == []
