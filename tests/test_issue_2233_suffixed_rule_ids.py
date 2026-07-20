"""
Regression tests for GitHub issue #2233:
sync-architecture misattributes generic contract rule tests and drops suffixed rule IDs.

Red-green fixture verifies:
  1. Suffixed rule IDs (R1a, R2b) are preserved by parse_rule_ids.
  2. Test function names with suffix (test_R1a_*) are matched correctly.
  3. Bare docstring mentions of R1 are NOT attributed (scope fix).
  4. build_coverage retains all declared IDs including suffixed ones.
  5. Two prompts both declaring R1, one declaring R1a: scoped sync
     does not bleed unrelated test evidence into either prompt.
"""
from __future__ import annotations

import textwrap
from pathlib import Path

import pytest

from pdd.coverage_contracts import (
    _parse_rule_ids,
    _scan_test_file,
    build_coverage,
    build_coverage_directory,
    scan_test_evidence,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _make_prompt(tmp_path: Path, content: str, name: str = "test_python.prompt") -> Path:
    p = tmp_path / name
    p.write_text(textwrap.dedent(content), encoding="utf-8")
    return p


def _make_test_file(tmp_path: Path, content: str, name: str = "test_foo.py") -> Path:
    p = tmp_path / name
    p.write_text(textwrap.dedent(content), encoding="utf-8")
    return p


# ===========================================================================
# 1. parse_rule_ids preserves suffixed IDs
# ===========================================================================

class TestParseRuleIdsPreservesSuffixedIds:
    def test_suffixed_id_r1a_preserved(self):
        text = "R1 - main rule\nR1a - sub-rule\nR2 - another rule"
        ids = _parse_rule_ids(text)
        assert "R1A" in ids, "R1a should be parsed and normalised to R1A"

    def test_all_three_ids_present_in_order(self):
        text = "R1 - main rule\nR1a - sub-rule\nR2 - another rule"
        ids = _parse_rule_ids(text)
        assert ids == ["R1", "R1A", "R2"]

    def test_suffixed_id_not_deduplicated_with_base(self):
        """R1 and R1a are distinct rules; neither should be dropped."""
        text = "R1 - base\nR1a - sub"
        ids = _parse_rule_ids(text)
        assert "R1" in ids
        assert "R1A" in ids
        assert len(ids) == 2

    def test_uppercase_suffix_normalised(self):
        text = "R1A - sub-rule uppercase"
        ids = _parse_rule_ids(text)
        assert "R1A" in ids

    def test_lowercase_suffix_normalised_to_uppercase(self):
        text = "R1a - sub-rule lowercase"
        ids = _parse_rule_ids(text)
        assert "R1A" in ids
        assert "R1a" not in ids


# ===========================================================================
# 2. Test function names with suffix are matched
# ===========================================================================

class TestScanTestSuffixedFunctionNames:
    def test_function_name_with_alpha_suffix(self, tmp_path):
        _make_test_file(tmp_path, "def test_R1a_validates_subcase():\n    pass\n")
        evidence = scan_test_evidence(tmp_path)
        assert "R1A" in evidence, "test_R1a_* should attribute to R1A"
        assert "test_R1a_validates_subcase" in evidence["R1A"]

    def test_base_function_name_still_works(self, tmp_path):
        _make_test_file(tmp_path, "def test_R1_validates():\n    pass\n")
        evidence = scan_test_evidence(tmp_path)
        assert "R1" in evidence

    def test_suffix_does_not_bleed_into_base(self, tmp_path):
        _make_test_file(tmp_path, "def test_R1a_validates():\n    pass\n")
        evidence = scan_test_evidence(tmp_path)
        # R1A should be present, but bare R1 should not (unless pattern 2/3 adds it)
        assert "R1A" in evidence
        assert "R1" not in evidence

    def test_comment_with_suffixed_id(self, tmp_path):
        content = "def test_something():  # R1a: sub-rule check\n    pass\n"
        _make_test_file(tmp_path, content)
        evidence = scan_test_evidence(tmp_path)
        assert "R1A" in evidence

    def test_docstring_explicit_colon_with_suffix(self, tmp_path):
        content = 'def test_foo():\n    """R1a: validates sub-rule."""\n    pass\n'
        _make_test_file(tmp_path, content)
        evidence = scan_test_evidence(tmp_path)
        assert "R1A" in evidence


# ===========================================================================
# 3. Bare docstring mentions are NOT attributed (scope-limit fix)
# ===========================================================================

class TestDocstringScopeLimit:
    def test_bare_mention_in_docstring_not_attributed(self, tmp_path):
        """A test whose docstring mentions 'R1' without colon/dash must not be attributed."""
        content = 'def test_unrelated():\n    """This validates the R1 algorithm."""\n    pass\n'
        _make_test_file(tmp_path, content)
        evidence = scan_test_evidence(tmp_path)
        assert "R1" not in evidence, "bare 'R1' in docstring must not attribute"

    def test_bare_mention_suffix_not_attributed(self, tmp_path):
        content = 'def test_unrelated():\n    """Uses R1a internally."""\n    pass\n'
        _make_test_file(tmp_path, content)
        evidence = scan_test_evidence(tmp_path)
        assert "R1A" not in evidence

    def test_explicit_colon_form_is_attributed(self, tmp_path):
        """R5: in docstring first line must still attribute."""
        content = 'def test_foo():\n    """R5: covers idempotency."""\n    pass\n'
        _make_test_file(tmp_path, content)
        evidence = scan_test_evidence(tmp_path)
        assert "R5" in evidence

    def test_explicit_dash_form_is_attributed(self, tmp_path):
        """R5 - description form must still attribute."""
        content = 'def test_foo():\n    """R5 - validates boundary."""\n    pass\n'
        _make_test_file(tmp_path, content)
        evidence = scan_test_evidence(tmp_path)
        assert "R5" in evidence

    def test_scan_test_file_bare_docstring_not_attributed(self):
        source = 'def test_unrelated():\n    """Tests the R2 pipeline."""\n    pass\n'
        evidence: dict = {}
        _scan_test_file(source, evidence, prompt_name="", require_prompt_qualified=False)
        assert "R2" not in evidence

    def test_scan_test_file_explicit_docstring_attributed(self):
        source = 'def test_foo():\n    """R2: validates pipeline."""\n    pass\n'
        evidence: dict = {}
        _scan_test_file(source, evidence, prompt_name="", require_prompt_qualified=False)
        assert "R2" in evidence


# ===========================================================================
# 4. build_coverage retains all declared IDs including suffixed ones
# ===========================================================================

class TestBuildCoveragePreservesSuffixedIds:
    def test_all_declared_ids_appear_in_rules(self, tmp_path):
        prompt = _make_prompt(
            tmp_path,
            """\
            <contract_rules>
            R1 - main rule
            The system MUST do R1.
            R1a - sub-rule of R1
            The system MUST also satisfy R1a.
            R2 - another rule
            The system MUST do R2.
            </contract_rules>
            """,
        )
        result = build_coverage(
            prompt,
            stories_dir=tmp_path / "stories",
            tests_dir=tmp_path / "tests",
        )
        rule_ids = [r.rule_id for r in result.rules]
        assert "R1" in rule_ids, "R1 must appear in coverage rules"
        assert "R1A" in rule_ids, "R1A (suffixed) must appear in coverage rules"
        assert "R2" in rule_ids, "R2 must appear in coverage rules"
        assert len(rule_ids) == 3

    def test_suffixed_rule_is_unchecked_when_no_evidence(self, tmp_path):
        prompt = _make_prompt(
            tmp_path,
            """\
            <contract_rules>
            R1 - main rule
            The system MUST do R1.
            R1a - sub-rule
            The system MUST also satisfy R1a.
            </contract_rules>
            """,
        )
        result = build_coverage(
            prompt,
            stories_dir=tmp_path / "stories",
            tests_dir=tmp_path / "tests",
        )
        r1a = next((r for r in result.rules if r.rule_id == "R1A"), None)
        assert r1a is not None, "R1A rule must be present"
        assert r1a.status == "unchecked"

    def test_suffixed_rule_gets_test_evidence(self, tmp_path):
        prompt = _make_prompt(
            tmp_path,
            """\
            <contract_rules>
            R1 - main rule
            The system MUST do R1.
            R1a - sub-rule
            The system MUST also satisfy R1a.
            </contract_rules>
            """,
        )
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        _make_test_file(
            tests_dir,
            "def test_R1a_validates_subcase():\n    pass\n",
        )
        result = build_coverage(
            prompt,
            stories_dir=tmp_path / "stories",
            tests_dir=tests_dir,
        )
        r1a = next((r for r in result.rules if r.rule_id == "R1A"), None)
        assert r1a is not None
        assert "test_R1a_validates_subcase" in r1a.tests


# ===========================================================================
# 5. Red-green regression: two prompts define R1, one defines R1a
# ===========================================================================

class TestRegressionTwoPromptsSuffixedId:
    """Issue #2233 core regression.

    Two prompts both declaring R1 plus one declaring R1a must:
    - Retain R1A in the declaring prompt's coverage.
    - Not bleed unrelated tests (bare docstring mentions) into any prompt.
    """

    def _setup(self, tmp_path: Path):
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()

        # Prompt A: defines R1, R1a, R2
        _make_prompt(
            prompts_dir,
            """\
            <contract_rules>
            R1 - main rule for A
            A MUST satisfy R1.
            R1a - sub-rule for A
            A MUST also satisfy R1a.
            R2 - second rule for A
            A MUST satisfy R2.
            </contract_rules>
            """,
            name="module_a.prompt",
        )

        # Prompt B: also defines R1 and R2 (different module, no R1a)
        _make_prompt(
            prompts_dir,
            """\
            <contract_rules>
            R1 - first rule for B
            B MUST satisfy R1.
            R2 - second rule for B
            B MUST satisfy R2.
            </contract_rules>
            """,
            name="module_b.prompt",
        )

        # Explicitly linked test for module_a R1a (function name pattern)
        _make_test_file(
            tests_dir,
            "def test_R1a_module_a_subcase():\n    pass\n",
            name="test_module_a.py",
        )

        # Unrelated tests that mention R1 and R2 only via bare docstring
        _make_test_file(
            tests_dir,
            """\
def test_unrelated_uses_R1_internally():
    '''This helper uses the R1 algorithm.'''
    pass

def test_another_R2_thing():
    '''Validates our R2 dependency.'''
    pass
""",
            name="test_unrelated.py",
        )

        return prompts_dir, stories_dir, tests_dir

    def test_module_a_retains_r1a(self, tmp_path):
        prompts_dir, stories_dir, tests_dir = self._setup(tmp_path)
        results = build_coverage_directory(
            prompts_dir, stories_dir=stories_dir, tests_dir=tests_dir
        )
        result_a = next(r for r in results if r.path.name == "module_a.prompt")
        rule_ids = {r.rule_id for r in result_a.rules}
        assert "R1" in rule_ids, "R1 must be declared in module_a"
        assert "R1A" in rule_ids, "R1A must be retained in module_a (issue #2233 fix)"
        assert "R2" in rule_ids, "R2 must be declared in module_a"

    def test_module_b_has_no_r1a(self, tmp_path):
        prompts_dir, stories_dir, tests_dir = self._setup(tmp_path)
        results = build_coverage_directory(
            prompts_dir, stories_dir=stories_dir, tests_dir=tests_dir
        )
        result_b = next(r for r in results if r.path.name == "module_b.prompt")
        rule_ids = {r.rule_id for r in result_b.rules}
        assert "R1A" not in rule_ids, "R1A must not appear in module_b which doesn't declare it"

    def test_unrelated_bare_docstring_tests_not_attributed(self, tmp_path):
        """In single-prompt mode, bare docstring mentions must not misattribute."""
        prompts_dir, stories_dir, tests_dir = self._setup(tmp_path)

        # Build single-prompt coverage for module_a (default: require_prompt_qualified=False)
        prompt_a = prompts_dir / "module_a.prompt"
        result_a = build_coverage(
            prompt_a, stories_dir=stories_dir, tests_dir=tests_dir
        )
        r1 = next(r for r in result_a.rules if r.rule_id == "R1")
        r2 = next(r for r in result_a.rules if r.rule_id == "R2")
        # Unrelated tests with bare mentions must not appear
        assert "test_unrelated_uses_R1_internally" not in r1.tests
        assert "test_another_R2_thing" not in r2.tests

    def test_explicitly_named_test_attributed_to_r1a(self, tmp_path):
        """test_R1a_module_a_subcase must be attributed to R1A in single-prompt mode."""
        prompts_dir, stories_dir, tests_dir = self._setup(tmp_path)
        prompt_a = prompts_dir / "module_a.prompt"
        result_a = build_coverage(
            prompt_a, stories_dir=stories_dir, tests_dir=tests_dir
        )
        r1a = next(r for r in result_a.rules if r.rule_id == "R1A")
        assert "test_R1a_module_a_subcase" in r1a.tests
