"""Tests for the warrant content review.

Every case is a shape that misled the review on 2026-09-10 before it was fixed,
because the ones that mislead are the ones worth pinning.
"""

from __future__ import annotations

import json

import pytest

import warrant_review as wr


@pytest.fixture
def workspace(tmp_path, monkeypatch):
    (tmp_path / "proofsense").mkdir()
    ocr = tmp_path / "ocr"
    ocr.mkdir()
    (tmp_path / "pdfs").mkdir()
    lean = tmp_path / "lean" / "EllipticPdes"
    lean.mkdir(parents=True)
    monkeypatch.setattr(wr, "ROOT", tmp_path)
    monkeypatch.setattr(wr, "MANIFEST", tmp_path / "proofsense" / "manifest.json")
    monkeypatch.setattr(wr, "OCR", ocr)
    monkeypatch.setattr(wr, "PDFS", tmp_path / "pdfs")

    def write(warrants, blocks, divergences=None, lean_src=""):
        doc = {"warrants": warrants}
        if divergences:
            doc["source_divergences"] = divergences
        (tmp_path / "proofsense" / "manifest.json").write_text(
            json.dumps(doc), encoding="utf-8")
        (ocr / "evans-2010-par-dif-equ.jsonl").write_text(
            json.dumps({"page": 1, "blocks": [{"text": b} for b in blocks]}) + "\n",
            encoding="utf-8")
        if lean_src:
            (lean / "A.lean").write_text(lean_src, encoding="utf-8")

    return write


def _w(claim, locator="§6.2.2 Thm 2", decl="EllipticPdes.t"):
    return {"decl": decl, "source_id": "evans-2010", "locator": locator, "claim": claim}


# clauses


def test_a_claim_silent_about_an_enumerated_statement_is_found(workspace):
    """Evans §6.2.2 Theorem 2 states boundedness and Garding; `garding` gives one."""
    workspace([_w("formalises")],
              ["6.2.2. SOMETHING", "THEOREM 2 (Energy estimates). There exist",
               "(i) boundedness", "(ii) the Garding inequality"])
    failures, _ = wr.review()
    assert failures and "names no clause" in failures[0]


def test_a_claim_naming_its_clause_passes(workspace):
    workspace([_w("formalises clause (ii), the Garding inequality")],
              ["6.2.2. SOMETHING", "THEOREM 2 (Energy estimates). There exist",
               "(i) boundedness", "(ii) the Garding inequality"])
    assert wr.review()[0] == []


def test_a_claim_saying_it_covers_the_whole_passes(workspace):
    """"in full", "at once" and "the local half" say the scope without a marker."""
    workspace([_w("formalises the theorem in full")],
              ["6.2.2. X", "THEOREM 2 (Energy estimates).", "(i) one", "(ii) two"])
    assert wr.review()[0] == []


def test_a_set_named_in_a_claim_is_not_a_clause_marker(workspace):
    """`W^{k,p}(V)` was read as clause (v) while the claim named clause (iii)."""
    workspace([_w("formalises clause (iii); the integrability of W^{k,p}(V) is inherited")],
              ["6.2.2. X", "THEOREM 2.", "(i) one", "(ii) two", "(iii) three"])
    _, readings = wr.review()
    assert not any("clause (v)" in r for r in readings)


# extraction


def test_a_section_local_number_is_read_from_its_own_section(workspace):
    """`§5.2.3 Thm 1` is not the first `THEOREM 1` after the contents page."""
    workspace([], ["5.1 Holder spaces", "5.2.3 Elementary properties",
                   "5.1. HOLDER SPACES", "THEOREM 1 (Holder spaces are Banach).",
                   "5.2.3. ELEMENTARY PROPERTIES",
                   "THEOREM 1 (Properties of weak derivatives)."])
    blocks = wr._source_text("evans-2010-par-dif-equ")
    got = wr.statement(blocks, "Thm", "1", "5.2.3")
    assert "Properties of weak derivatives" in got


def test_remarks_after_a_statement_are_not_clauses_of_it(workspace):
    workspace([], ["6.3.2. X", "THEOREM 4 (Boundary regularity). Assume",
                   "Remarks. (i) If u is the unique weak solution", "(ii) and so on"])
    blocks = wr._source_text("evans-2010-par-dif-equ")
    got = wr.statement(blocks, "Thm", "4", "6.3.2")
    assert "Remarks" not in got


# recorded divergences


def test_a_hypothesis_the_signature_lacks_is_reported(workspace):
    workspace([_w("formalises clause (i)", locator="§6.3.1 Thm 1")],
              ["6.3.1. X", "THEOREM 1. Suppose u \\in H ^ { 1 } ( U ) is a weak solution",
               "(i) one", "(ii) two"],
              lean_src="theorem t : True := trivial\n")
    _, readings = wr.review()
    assert any("H^1" in r for r in readings)


def test_a_recorded_divergence_settles_the_reading(workspace):
    workspace([_w("formalises clause (i)", locator="§6.3.1 Thm 1")],
              ["6.3.1. X", "THEOREM 1. Suppose u \\in H ^ { 1 } ( U ) is a weak solution",
               "(i) one", "(ii) two"],
              divergences=[{"source_id": "evans-2010", "locator": "§6.3.1 Thm 1",
                            "labels": ["H^1 (not H_0^1)"],
                            "note": "the chain takes the solution in H_0^1"}],
              lean_src="theorem t : True := trivial\n")
    _, readings = wr.review()
    assert not any("H^1" in r for r in readings)
