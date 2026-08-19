import proofsense_coverage as pc


def warrant(decl, locator="§6.3.1 Thm 1"):
    return {"decl": decl, "source_id": "evans-2010", "locator": locator}


def test_the_audit_parses_the_printed_declarations(tmp_path):
    f = tmp_path / "AxiomAudit.lean"
    f.write_text(
        "import EllipticPdes\n"
        "/-- info: 'A.b' depends on axioms: [propext] -/\n"
        "#guard_msgs (whitespace := lax) in\n"
        "#print axioms A.b\n"
        "#print axioms C.d\n"
    )
    assert pc.audited_declarations(f) == ["A.b", "C.d"]


def test_a_warranted_audited_declaration_passes():
    assert pc.check(["A.b"], [warrant("A.b")], {}) == []


def test_an_unwarranted_audited_declaration_fails():
    failures = pc.check(["A.b"], [], {})
    assert len(failures) == 1
    assert "carries no warrant" in failures[0]


def test_an_exemption_covers_an_audited_declaration():
    assert pc.check(["A.b"], [], {"A.b": "no transcribed target"}) == []


def test_a_stale_exemption_fails():
    failures = pc.check(["A.b"], [warrant("A.b")], {"C.d": "gone"})
    assert any("no longer audits it" in f for f in failures)


def test_being_both_warranted_and_exempt_fails():
    failures = pc.check(["A.b"], [warrant("A.b")], {"A.b": "why"})
    assert any("both warranted and exempt" in f for f in failures)


def test_a_warrant_on_an_unaudited_declaration_fails():
    failures = pc.check(["A.b"], [warrant("A.b"), warrant("X.y")], {})
    assert any("does not audit it" in f for f in failures)


def test_a_section_locator_fails():
    failures = pc.check(["A.b"], [warrant("A.b", "§6.3.1")], {})
    assert len(failures) == 1
    assert "names a section" in failures[0]


def test_every_statement_marker_spelling_is_accepted():
    for locator in (
        "§6.3.1 Thm 1",
        "6.3.1 Theorem 1",
        "§8.2 Lem 3",
        "§8.2 Corollary 12",
        "§1.1 Def 2",
        "§1.1 Remark 4",
        "§6.3.1 thm 1",
    ):
        assert pc.check(["A.b"], [warrant("A.b", locator)], {}) == [], locator


def test_a_named_statement_in_an_unnumbered_section_is_accepted():
    """Fernandez-Real and Ros-Oton leave several chapter theorems unnumbered."""
    for locator in (
        "§1.1 Thm (Sobolev inequality)",
        "§2.5 Theorem (Schauder estimates in divergence form)",
        "§2.5 Cor (higher order)",
    ):
        assert pc.check(["A.b"], [warrant("A.b", locator)], {}) == [], locator


def test_a_labelled_appendix_property_is_accepted():
    """The same text numbers its Holder-space appendix properties (H1) to (H8)."""
    for locator in ("App. A (H3)", "App A (H1)", "Appendix B (P2)"):
        assert pc.check(["A.b"], [warrant("A.b", locator)], {}) == [], locator


def test_a_bare_appendix_locator_still_fails():
    """Widening the rule must not admit a whole appendix."""
    for locator in ("App. A", "Appendix A", "§1.1 Thm"):
        failures = pc.check(["A.b"], [warrant("A.b", locator)], {})
        assert len(failures) == 1, locator
        assert "names a section" in failures[0], locator


def test_the_repository_is_covered():
    """Run against the real AxiomAudit.lean and the real manifest."""
    import json

    audited = pc.audited_declarations(pc.AUDIT)
    warrants = json.loads(pc.MANIFEST.read_text(encoding="utf-8"))["warrants"]
    assert pc.check(audited, warrants, pc.EXEMPT) == []
