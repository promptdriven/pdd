# pylint: disable=too-many-lines
"""
Contract coverage matrix engine.

Builds a rule-to-evidence map for `.prompt` files that contain
`<contract_rules>`, showing which rules are checked, story-only, test-only,
unchecked, or waived.  No LLM required.

Public API
----------
build_coverage(path, stories_dir, tests_dir) -> CoverageResult
build_coverage_directory(directory, stories_dir, tests_dir) -> list[CoverageResult]
"""
from __future__ import annotations

import ast
import logging
import re
import warnings
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Status constants
# ---------------------------------------------------------------------------

STATUS_CHECKED = "checked"
STATUS_STORY_ONLY = "story-only"
STATUS_TEST_ONLY = "test-only"
STATUS_UNCHECKED = "unchecked"
STATUS_WAIVED = "waived"
STATUS_FAILED = "failed"
STATUS_FORMAL_ONLY = "formal-only"
STATUS_NEEDS_HUMAN = "needs-human"

# ---------------------------------------------------------------------------
# Section extraction (canonical parser in contract_ir)
# ---------------------------------------------------------------------------

from .contract_ir import (  # noqa: E402
    extract_sections as _extract_sections,
    parse_coverage_block as _parse_coverage_block,
    parse_prompt_contracts,
    parse_rule_ids as _parse_rule_ids,
    parse_waiver_rule_map as _parse_waiver_rule_map,
)

_MARKDOWN_HEADING_RE = re.compile(
    r"^#{1,3}\s+(?P<heading>.+?)\s*$",
    re.MULTILINE,
)


def _extract_markdown_section(text: str, heading: str) -> str:
    """
    Return the text under a specific markdown heading until the next heading.
    Case-insensitive heading match.
    """
    pattern = re.compile(
        r"^#{1,3}\s+" + re.escape(heading) + r"\s*$(.*?)(?=^#{1,3}\s|\Z)",
        re.MULTILINE | re.DOTALL | re.IGNORECASE,
    )
    match = pattern.search(text)
    return match.group(1).strip() if match else ""

# ---------------------------------------------------------------------------
# Rule ID patterns (mirrors contract_check.py)
# ---------------------------------------------------------------------------

_EXPLICIT_ID_RE = re.compile(r"^(R-?\d+|RULE-?\d+)\b", re.IGNORECASE)
_SEQ_ID_RE = re.compile(r"^(\d+)[.):\s]")
_COVERAGE_REF_RE = re.compile(r"\b(R-?\d+|RULE-?\d+)\b", re.IGNORECASE)
_CROSS_MODULE_REF_RE = re.compile(
    r"([\w./\-]+\.prompt)#(R-?\d+|RULE-?\d+)\b", re.IGNORECASE
)
_WAIVER_ID_RE = re.compile(r"^(W-?\d+):", re.IGNORECASE)
_WAIVER_REF_RE = re.compile(r"\bWAIVED\s+(W-?\d+)\b", re.IGNORECASE)
_STORY_PROMPTS_META_RE = re.compile(
    r"<!--\s*pdd-story-prompts:\s*(?P<prompts>.*?)\s*-->",
    re.IGNORECASE,
)

# Test-name heuristic patterns
# Matches: test_R1_something  test_r2_foo  testR3bar
_TEST_FUNC_RE = re.compile(r"\btest[_]?[Rr](\d+)[_\b]", re.IGNORECASE)
# Inline comment: # R1:  # covers R2  # rule R3
_TEST_COMMENT_RE = re.compile(
    r"#\s*(?:covers\s+|rule\s+)?(R-?\d+)\b", re.IGNORECASE
)

# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------


@dataclass
class StoryEvidence:
    """Story-level coverage evidence with validation status."""

    path: str
    validation: str = "passed"  # passed | failed | unknown

    def as_dict(self) -> dict:
        return {"path": self.path, "validation": self.validation}


@dataclass
class RuleCoverage:
    """Coverage evidence for one contract rule."""

    rule_id: str
    status: str          # STATUS_* constant
    stories: list[str] = field(default_factory=list)   # story filenames
    tests: list[str] = field(default_factory=list)     # test function names
    formal: list[str] = field(default_factory=list)    # formalization evidence
    waiver: Optional[str] = None                       # waiver ID, e.g. "W1"
    failures: list[str] = field(default_factory=list)  # validation failures
    notes: list[str] = field(default_factory=list)
    story_details: list[StoryEvidence] = field(default_factory=list)

    def as_dict(self) -> dict:
        """Serialise to a JSON-safe dictionary."""
        return {
            "rule_id": self.rule_id,
            "status": self.status,
            "stories": self.stories,
            "tests": self.tests,
            "formal": self.formal,
            "waiver": self.waiver,
            "failures": self.failures,
            "notes": self.notes,
            "story_details": [s.as_dict() for s in self.story_details],
        }


@dataclass
class CoverageResult:
    """Coverage matrix for one prompt file."""

    path: Path
    rules: list[RuleCoverage] = field(default_factory=list)
    has_contract_rules: bool = False
    error: Optional[str] = None

    @property
    def summary(self) -> dict[str, int]:
        """Return per-status counts."""
        counts: dict[str, int] = {
            "total": len(self.rules),
            "checked": 0,
            "story_only": 0,
            "test_only": 0,
            "unchecked": 0,
            "waived": 0,
            "failed": 0,
            "formal_only": 0,
            "needs_human": 0,
        }
        for rule in self.rules:
            key = rule.status.replace("-", "_")
            if key in counts:
                counts[key] += 1
        return counts

    def as_dict(self) -> dict:
        """Serialise to a JSON-safe dictionary."""
        return {
            "path": str(self.path),
            "has_contract_rules": self.has_contract_rules,
            "error": self.error,
            "rules": [r.as_dict() for r in self.rules],
            "summary": self.summary,
        }

# ---------------------------------------------------------------------------
# Section parsers
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Story evidence scanner
# ---------------------------------------------------------------------------


def _prompt_basename(path: Path) -> str:
    """Return just the filename of a prompt path, e.g. 'foo_python.prompt'."""
    return path.name


def _story_links_prompt(story_text: str, prompt_name: str) -> bool:
    """
    Return True if the story's pdd-story-prompts metadata mentions prompt_name.
    If the metadata comment is absent, the story is considered potentially
    linked to any prompt (broad match).
    """
    meta_match = _STORY_PROMPTS_META_RE.search(story_text)
    if not meta_match:
        return False  # no metadata = not linked to any specific prompt
    prompts_str = meta_match.group("prompts")
    listed = [p.strip() for p in prompts_str.split(",")]
    prompt_base = prompt_name.lower()
    return any(
        p.lower() == prompt_base or p.lower().endswith("/" + prompt_base)
        for p in listed
    )


def _rule_ids_from_covers(covers_text: str, prompt_name: str) -> set[str]:
    """
    Extract rule IDs referenced in a ## Covers block for a given prompt.

    Handles both formats:
      - R1: description                       (single-prompt)
      - prompts/foo.prompt#R3: description    (cross-module)
    """
    ids: set[str] = set()
    for line in covers_text.splitlines():
        stripped = line.strip().lstrip("-* ")
        if not stripped:
            continue
        # Cross-module: prompt.prompt#R3
        for cross_match in _CROSS_MODULE_REF_RE.finditer(stripped):
            ref_file = cross_match.group(1).rsplit("/", 1)[-1]
            if ref_file.lower() == prompt_name.lower():
                ids.add(cross_match.group(2).upper())
        if not _CROSS_MODULE_REF_RE.search(stripped):
            # Single-prompt format — any R<N> reference counts
            for ref_match in _COVERAGE_REF_RE.finditer(stripped):
                ids.add(ref_match.group(1).upper())
    return ids


def scan_story_evidence(
    stories_dir: Path,
    prompt_path: Path,
) -> dict[str, list[str]]:
    """
    Scan story__*.md files (recursively) and return a mapping
    rule_id → [story_filename, ...] for rules covered by stories
    that link to prompt_path.

    The story must have a <!-- pdd-story-prompts: ... --> comment
    that includes the prompt's filename (or relative path).
    """
    evidence: dict[str, list[str]] = {}
    if not stories_dir.exists():
        return evidence

    prompt_name = _prompt_basename(prompt_path)

    for story_path in sorted(stories_dir.rglob("story__*.md")):
        try:
            story_text = story_path.read_text(encoding="utf-8")
        except OSError:
            continue

        if not _story_links_prompt(story_text, prompt_name):
            continue

        covers_text = _extract_markdown_section(story_text, "Covers")
        if not covers_text:
            continue

        rule_ids = _rule_ids_from_covers(covers_text, prompt_name)
        for rid in rule_ids:
            evidence.setdefault(rid, [])
            if story_path.name not in evidence[rid]:
                evidence[rid].append(story_path.name)

    return evidence


def scan_story_validation_failures(
    stories_dir: Path,
    prompt_path: Path,
) -> dict[str, list[str]]:
    """
    Return rule_id -> validation failure descriptions for linked stories.

    This is intentionally deterministic and uses the existing story-linking
    convention: only stories with pdd-story-prompts metadata matching the prompt
    are considered. A linked story that claims rule coverage but has no
    ``## Acceptance Criteria`` section is considered failed coverage evidence.
    """
    failures: dict[str, list[str]] = {}
    if not stories_dir.exists():
        return failures

    prompt_name = _prompt_basename(prompt_path)

    for story_path in sorted(stories_dir.rglob("story__*.md")):
        try:
            story_text = story_path.read_text(encoding="utf-8")
        except OSError as exc:
            failures.setdefault("__story_read_error__", []).append(
                f"{story_path.name}: {exc}"
            )
            continue

        if not _story_links_prompt(story_text, prompt_name):
            continue

        covers_text = _extract_markdown_section(story_text, "Covers")
        if not covers_text:
            continue

        rule_ids = _rule_ids_from_covers(covers_text, prompt_name)
        if not rule_ids:
            continue

        acceptance_text = _extract_markdown_section(story_text, "Acceptance Criteria")
        if acceptance_text.strip():
            continue

        for rid in rule_ids:
            failures.setdefault(rid, [])
            failures[rid].append(
                f"{story_path.name}: missing ## Acceptance Criteria"
            )

    return failures

# ---------------------------------------------------------------------------
# Test evidence scanner (heuristic)
# ---------------------------------------------------------------------------

# DOCUMENTED HEURISTIC:
# This scanner finds test functions that explicitly reference a rule ID.
# It does NOT parse test logic or assertions.  Recognised patterns:
#   1. Function name:  test_R1_something  test_r2_foo  (case-insensitive)
#   2. Inline comment: # R1:  # covers R2  # rule R3  (anywhere in the file)
#   3. Docstring first line: containing "R1:" or "R1 -" within 120 chars
# Only patterns that a developer explicitly chose to write are matched.
# No fuzzy or semantic matching is performed.


def scan_test_evidence(tests_dir: Path) -> dict[str, list[str]]:
    """
    Heuristically scan test files for rule ID references.

    Returns mapping rule_id → [test_function_name, ...].
    Only test functions (names starting with "test_") that explicitly
    reference a rule ID are included.

    See module docstring for the documented heuristic.
    """
    evidence: dict[str, list[str]] = {}
    if not tests_dir.exists():
        return evidence

    for test_file in sorted(tests_dir.rglob("test_*.py")):
        try:
            source = test_file.read_text(encoding="utf-8")
        except OSError:
            continue

        _scan_test_file(source, evidence)

    return evidence


def scan_test_validation_failures(tests_dir: Path) -> dict[str, list[str]]:
    """
    Return rule_id -> validation failure descriptions for test files.

    The v1 coverage scanner does not execute tests. The deterministic failure
    check is therefore limited to syntax validation: a test_*.py file that
    cannot be parsed and explicitly references R<N> is failed evidence for
    those rules.
    """
    failures: dict[str, list[str]] = {}
    if not tests_dir.exists():
        return failures

    for test_file in sorted(tests_dir.rglob("test_*.py")):
        try:
            source = test_file.read_text(encoding="utf-8")
        except OSError as exc:
            failures.setdefault("__test_read_error__", []).append(
                f"{test_file.name}: {exc}"
            )
            continue

        try:
            with warnings.catch_warnings():
                warnings.simplefilter("ignore", SyntaxWarning)
                ast.parse(source)
        except SyntaxError as exc:
            referenced_rules = _rule_ids_from_test_source(source)
            for rid in referenced_rules:
                failures.setdefault(rid, [])
                failures[rid].append(
                    f"{test_file.name}: syntax error on line {exc.lineno or '?'}"
                )

    return failures


def _rule_ids_from_test_source(source: str) -> set[str]:
    """Extract explicit rule IDs from a possibly invalid test file."""
    ids: set[str] = set()
    for digit in _TEST_FUNC_RE.findall(source):
        ids.add(f"R{digit}")
    for comment_match in _TEST_COMMENT_RE.finditer(source):
        ids.add(comment_match.group(1).upper())
    for ref_match in _COVERAGE_REF_RE.finditer(source):
        ids.add(ref_match.group(1).upper())
    return ids


def _scan_test_file(source: str, evidence: dict[str, list[str]]) -> None:  # pylint: disable=too-many-locals
    """
    Parse a single test file's source and populate evidence in-place.

    Uses AST for function-name and docstring checks; regex for comments.
    """
    try:
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", SyntaxWarning)
            tree = ast.parse(source)
    except SyntaxError:
        # Fall back to regex-only scanning
        _scan_test_file_regex(source, evidence)
        return

    # Map line number → comment text for comment scanning
    comment_by_line: dict[int, str] = {}
    for line_no, line in enumerate(source.splitlines(), 1):
        comment_match = _TEST_COMMENT_RE.search(line)
        if comment_match:
            rid = comment_match.group(1).upper()
            comment_by_line.setdefault(line_no, rid)

    for node in ast.walk(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        fname = node.name
        if not fname.startswith("test"):
            continue

        # Pattern 1: function name contains R<N>
        name_matches = _TEST_FUNC_RE.findall(fname)
        for digit in name_matches:
            rid = f"R{digit}"
            evidence.setdefault(rid, [])
            if fname not in evidence[rid]:
                evidence[rid].append(fname)

        # Pattern 2: comment on the function definition line or within 2 lines
        for line_offset in range(3):
            target_line = node.lineno + line_offset
            if target_line in comment_by_line:
                rid = comment_by_line[target_line]
                evidence.setdefault(rid, [])
                if fname not in evidence[rid]:
                    evidence[rid].append(fname)

        # Pattern 3: first line of docstring
        docstring = ast.get_docstring(node)
        if docstring:
            first_line = docstring.splitlines()[0][:120]
            for doc_match in _COVERAGE_REF_RE.finditer(first_line):
                rid = doc_match.group(1).upper()
                evidence.setdefault(rid, [])
                if fname not in evidence[rid]:
                    evidence[rid].append(fname)


def _scan_test_file_regex(source: str, evidence: dict[str, list[str]]) -> None:
    """Fallback regex-only scanner used when AST parsing fails."""
    for line in source.splitlines():
        stripped = line.strip()
        if not stripped.startswith("def test"):
            continue
        fname_match = re.match(r"def\s+(test\w+)", stripped)
        if not fname_match:
            continue
        fname = fname_match.group(1)
        for digit in _TEST_FUNC_RE.findall(fname):
            rid = f"R{digit}"
            evidence.setdefault(rid, [])
            if fname not in evidence[rid]:
                evidence[rid].append(fname)
        comment_match = _TEST_COMMENT_RE.search(line)
        if comment_match:
            rid = comment_match.group(1).upper()
            evidence.setdefault(rid, [])
            if fname not in evidence[rid]:
                evidence[rid].append(fname)

# ---------------------------------------------------------------------------
# Status classifier
# ---------------------------------------------------------------------------


def _classify_rule(  # pylint: disable=too-many-arguments
    rule_id: str,
    coverage_entries: dict[str, str],
    waiver_map: dict[str, str],
    story_evidence: dict[str, list[str]],
    test_evidence: dict[str, list[str]],
    validation_failures: Optional[dict[str, list[str]]] = None,
    formal_evidence: Optional[dict[str, list[str]]] = None,
    story_validation: Optional[dict[str, list[StoryEvidence]]] = None,
) -> RuleCoverage:
    """
    Classify one rule ID and return a RuleCoverage.

    Priority:
      1. Waived (explicit WAIVED W<N> in <coverage>, or <waivers> block)
      2. Failed (story/test validation failure)
      3. Checked (story + test)
      4. Story-only
      5. Test-only
      6. Unchecked
    """
    rid = rule_id.upper()
    coverage_text = coverage_entries.get(rid, "")

    # Check for explicit waiver
    waiver_id: Optional[str] = None
    waiver_ref = _WAIVER_REF_RE.search(coverage_text)
    if waiver_ref:
        waiver_id = waiver_ref.group(1).upper()
    elif rid in waiver_map:
        waiver_id = waiver_map[rid]

    if waiver_id:
        # Still collect any story evidence for display
        stories = story_evidence.get(rid, [])
        return RuleCoverage(
            rule_id=rid,
            status=STATUS_WAIVED,
            stories=stories,
            tests=[],
            waiver=waiver_id,
        )

    failures = list((validation_failures or {}).get(rid, []))
    if failures:
        return RuleCoverage(
            rule_id=rid,
            status=STATUS_FAILED,
            stories=list(story_evidence.get(rid, [])),
            tests=list(test_evidence.get(rid, [])),
            waiver=None,
            failures=failures,
        )

    # Gather story and test evidence
    stories = list(story_evidence.get(rid, []))
    tests = list(test_evidence.get(rid, []))

    # Also interpret <coverage> entries that look like test names
    if coverage_text and not coverage_text.upper().startswith("TODO"):
        # Split comma-separated explicit evidence such as:
        #   R1: story__foo.md, test_R1_bar
        # Keep each item in the proper evidence column.
        for evidence_item in [p.strip() for p in coverage_text.split(",") if p.strip()]:
            if evidence_item.lower().startswith("story__"):
                if evidence_item not in stories:
                    stories.append(evidence_item)
            elif "test" in evidence_item.lower() and evidence_item not in tests:
                tests.append(evidence_item)

    formal = list((formal_evidence or {}).get(rid, []))
    story_details = list((story_validation or {}).get(rid, []))
    has_story = bool(stories)
    has_test = bool(tests)
    has_formal = bool(formal)
    valid_story = bool(story_details) and all(
        s.validation == "passed" for s in story_details
    ) if story_details else has_story

    notes: list[str] = []
    if has_story and not has_test:
        notes.append(
            "Story validates prompt intent, but no executable test references "
            f"{rid}."
        )

    if valid_story and has_test:
        status = STATUS_CHECKED
    elif valid_story:
        status = STATUS_STORY_ONLY
    elif has_test:
        status = STATUS_TEST_ONLY
    elif has_formal:
        status = STATUS_FORMAL_ONLY
    else:
        status = STATUS_UNCHECKED

    return RuleCoverage(
        rule_id=rid,
        status=status,
        stories=stories,
        tests=tests,
        formal=formal,
        waiver=None,
        notes=notes,
        story_details=story_details,
    )

# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def build_coverage(
    path: Path,
    stories_dir: Optional[Path] = None,
    tests_dir: Optional[Path] = None,
    *,
    strict: bool = False,
) -> CoverageResult:
    """
    Build a coverage matrix for a single prompt file.

    Parameters
    ----------
    path:
        Path to the `.prompt` file.
    stories_dir:
        Directory to scan for `story__*.md` files (recursive).
        Defaults to `user_stories/` relative to cwd if not provided.
    tests_dir:
        Directory to scan for `test_*.py` files (recursive).
        Defaults to `tests/` relative to cwd if not provided.

    Returns
    -------
    CoverageResult with `has_contract_rules=False` and empty `rules`
    for legacy prompts that have no `<contract_rules>` section.
    """
    if stories_dir is None:
        stories_dir = Path("user_stories")
    if tests_dir is None:
        tests_dir = Path("tests")

    result = CoverageResult(path=path)

    ir = parse_prompt_contracts(path, stories_dir=stories_dir, tests_dir=tests_dir)
    if ir.parse_error:
        result.error = ir.parse_error
        return result

    if "contract_rules" not in ir.sections:
        return result

    result.has_contract_rules = True
    rules_text = ir.sections.get("contract_rules", "")
    if not rules_text.strip():
        return result
    rule_ids = _parse_rule_ids(rules_text)

    coverage_entries = dict(ir.coverage_entries)
    waivers_text = ir.sections.get("waivers", "")
    waiver_map = _parse_waiver_rule_map(waivers_text) if waivers_text else {}

    story_evidence = ir.story_covers or scan_story_evidence(stories_dir, path)
    test_evidence = ir.test_refs or scan_test_evidence(tests_dir)
    validation_failures: dict[str, list[str]] = {}
    for source in (
        scan_story_validation_failures(stories_dir, path),
        scan_test_validation_failures(tests_dir),
    ):
        for rid, messages in source.items():
            validation_failures.setdefault(rid, []).extend(messages)

    formal_evidence: dict[str, list[str]] = {}
    for formal in ir.formalizations:
        rid = formal.rule_id.upper()
        label = f"smt:{rid}" if (formal.target or "").lower() == "smt" else f"formal:{rid}"
        if formal.predicate:
            label = f"{label}:predicate"
        formal_evidence.setdefault(rid, []).append(label)

    story_validation: dict[str, list[StoryEvidence]] = {}
    for rid, story_names in story_evidence.items():
        fails = validation_failures.get(rid, [])
        for name in story_names:
            failed = any(name in msg for msg in fails)
            story_validation.setdefault(rid, []).append(
                StoryEvidence(path=name, validation="failed" if failed else "passed")
            )

    for rid in rule_ids:
        rule_cov = _classify_rule(
            rid,
            coverage_entries,
            waiver_map,
            story_evidence,
            test_evidence,
            validation_failures,
            formal_evidence=formal_evidence,
            story_validation=story_validation,
        )
        result.rules.append(rule_cov)

    if strict:
        for rule_cov in result.rules:
            rule = ir.rule_by_id(rule_cov.rule_id)
            modal = (rule.modal if rule else "").upper()
            if rule_cov.status == STATUS_FAILED:
                result.error = result.error or "strict coverage: failed evidence"
            elif rule_cov.status == STATUS_UNCHECKED and modal in ("MUST", "MUST NOT"):
                result.error = result.error or "strict coverage: uncovered MUST/MUST NOT"
            elif rule_cov.status == STATUS_STORY_ONLY and modal == "MUST NOT":
                result.error = result.error or "strict coverage: MUST NOT requires executable test"

    return result


def build_coverage_directory(
    directory: Path,
    stories_dir: Optional[Path] = None,
    tests_dir: Optional[Path] = None,
    *,
    strict: bool = False,
) -> list[CoverageResult]:
    """
    Build coverage matrices for every `*.prompt` file under a directory.

    Returns one CoverageResult per file, skipping `*_llm.prompt` files.
    """
    results: list[CoverageResult] = []
    for prompt_path in sorted(directory.rglob("*.prompt")):
        if prompt_path.name.lower().endswith("_llm.prompt"):
            continue
        results.append(
            build_coverage(prompt_path, stories_dir, tests_dir, strict=strict)
        )
    return results
