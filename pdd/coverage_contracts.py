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
import os
import posixpath
import re
import warnings
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

from .contract_ir import (
    COVERAGE_REF_RE,
    CROSS_MODULE_REF_RE,
    _WAIVER_REF_RE,
    _extract_markdown_sections,
    extract_waivers as _extract_waivers,
    extract_sections as _extract_sections,
    parse_coverage_block as _parse_coverage_block,
    parse_rule_ids as _parse_rule_ids,
    parse_waiver_rule_map as _parse_waiver_rule_map,
    rule_ids_from_covers as _rule_ids_from_covers,
)
from .waiver_policy import classify_waiver_status, waiver_id_to_rule_map

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
from .story_regression_gate import (  # noqa: E402  (status re-export)
    STATUS_STORY_REGRESSION_MISSING,
    STATUS_STORY_REGRESSION_STALE,
)

# ---------------------------------------------------------------------------
# Markdown section helper (uses contract_ir heading index)
# ---------------------------------------------------------------------------


def _extract_markdown_section(text: str, heading: str) -> str:
    """Return body under a markdown ## / ### heading (case-insensitive)."""
    return _extract_markdown_sections(text).get(heading.strip().lower(), "")


_STORY_PROMPTS_META_RE = re.compile(
    r"<!--\s*pdd-story-prompts:\s*(?P<prompts>.*?)\s*-->",
    re.IGNORECASE,
)

# Test-name heuristic patterns
# Matches: test_R1_something  test_r2_foo  testR3bar  test_R1a_sub
_TEST_FUNC_RE = re.compile(r"\btest[_]?[Rr](\d+[a-zA-Z]?)(?:_|\b)", re.IGNORECASE)
# Inline comment: # R1:  # covers R2  # rule R3  # R1a:
_TEST_COMMENT_RE = re.compile(
    r"#\s*(?:covers\s+|rule\s+)?(R-?\d+[a-zA-Z]?)\b", re.IGNORECASE
)
# Docstring explicit form: R1: text  or  R1 - text  (colon/dash required to avoid bare mentions)
_TEST_DOCSTRING_RE = re.compile(r"\b(R-?\d+[a-zA-Z]?)\s*[-:]", re.IGNORECASE)

# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------


@dataclass
class RuleCoverage:
    """Coverage evidence for one contract rule."""

    rule_id: str
    status: str          # STATUS_* constant
    stories: list[str] = field(default_factory=list)   # story filenames
    tests: list[str] = field(default_factory=list)     # test function names
    waiver: Optional[str] = None                       # waiver ID, e.g. "W1"
    waiver_status: Optional[str] = None                # active|expired|unknown-rule|malformed|untracked
    waiver_expires: Optional[str] = None               # ISO date
    failures: list[str] = field(default_factory=list)  # validation failures
    is_cross_unit: bool = False
    cross_unit_partners: list[str] = field(default_factory=list)

    def as_dict(self) -> dict:
        """Serialise to a JSON-safe dictionary."""
        return {
            "rule_id": self.rule_id,
            "status": self.status,
            "stories": self.stories,
            "tests": self.tests,
            "waiver": self.waiver,
            "waiver_status": self.waiver_status,
            "waiver_expires": self.waiver_expires,
            "failures": self.failures,
            "is_cross_unit": self.is_cross_unit,
            "cross_unit_partners": self.cross_unit_partners,
        }


@dataclass
class StoryRegression:
    """Per-story executable-regression-test dimension (orthogonal to rules).

    This is *story-keyed*, not rule-keyed: it records whether at least one
    collected pytest test claims the story via ``@pytest.mark.story``. It is
    deliberately kept off :class:`RuleCoverage`, which stays rule-keyed.
    """

    story_id: str
    has_regression_test: bool
    status: str
    tests: list[str] = field(default_factory=list)
    story_hash: Optional[str] = None

    def as_dict(self) -> dict:
        """Serialise to a JSON-safe dictionary."""
        return {
            "story_id": self.story_id,
            "has_regression_test": self.has_regression_test,
            "status": self.status,
            "tests": self.tests,
            "story_hash": self.story_hash,
        }


@dataclass
class CoverageResult:
    """Coverage matrix for one prompt file."""

    path: Path
    rules: list[RuleCoverage] = field(default_factory=list)
    has_contract_rules: bool = False
    error: Optional[str] = None
    read_errors: list[str] = field(default_factory=list)
    # Orthogonal, additive story-regression dimension (see StoryRegression).
    stories: list[StoryRegression] = field(default_factory=list)
    cross_unit_stories: list[str] = field(default_factory=list)
    # Validation warnings: a marker claims a story_id with no story__<slug>.md.
    # Distinct from the "story has no test" gap, which is a story with
    # ``has_regression_test=False`` in ``stories`` above.
    regression_warnings: list[str] = field(default_factory=list)

    @property
    def summary(self) -> dict[str, int]:
        """Return per-status counts (plus the orthogonal story-regression tally)."""
        counts: dict[str, int] = {
            "total": len(self.rules),
            "checked": 0,
            "story_only": 0,
            "test_only": 0,
            "unchecked": 0,
            "waived": 0,
            "failed": 0,
        }
        for rule in self.rules:
            key = rule.status.replace("-", "_")
            if key in counts:
                counts[key] += 1
        # Additive, orthogonal keys — they do not affect the rule-status counts.
        counts["stories_total"] = len(self.stories)
        counts["stories_with_regression_test"] = sum(
            1 for s in self.stories if s.has_regression_test
        )
        counts["story_regression_missing"] = sum(
            1 for s in self.stories if s.status == "story-regression-missing"
        )
        counts["story_regression_stale"] = sum(
            1 for s in self.stories if s.status == "story-regression-stale"
        )
        return counts

    def as_dict(self) -> dict:
        """Serialise to a JSON-safe dictionary."""
        return {
            "path": str(self.path),
            "has_contract_rules": self.has_contract_rules,
            "error": self.error,
            "read_errors": self.read_errors,
            "rules": [r.as_dict() for r in self.rules],
            "stories": [s.as_dict() for s in self.stories],
            "cross_unit_stories": self.cross_unit_stories,
            "regression_warnings": self.regression_warnings,
            "summary": self.summary,
        }

# ---------------------------------------------------------------------------
# Story evidence scanner
# ---------------------------------------------------------------------------


def _story_links_prompt(
    story_text: str,
    prompt_name: str,
    *,
    allow_prompt_basename: bool = True,
) -> bool:
    """
    Return True if the story's pdd-story-prompts metadata mentions prompt_name.

    Stories without ``<!-- pdd-story-prompts: ... -->`` are treated as applying
    to the prompt set under evaluation (matching the existing user-story flow).
    """
    meta_match = _STORY_PROMPTS_META_RE.search(story_text)
    if not meta_match:
        return True  # no metadata = applies to prompt set
    prompts_str = meta_match.group("prompts")
    listed = [p.strip() for p in prompts_str.split(",")]
    return any(
        _prompt_reference_matches(
            p,
            prompt_name,
            allow_basename=allow_prompt_basename,
        )
        for p in listed
    )


def scan_story_evidence(
    stories_dir: Path,
    prompt_path: Path,
    read_errors: Optional[list[str]] = None,
) -> dict[str, list[str]]:
    """
    Scan story__*.md files (recursively) and return a mapping
    rule_id → [story_filename, ...] for rules covered by stories
    that link to prompt_path.

    Story linking follows ``pdd/user_story_tests.py``: stories with
    ``<!-- pdd-story-prompts: ... -->`` must list the prompt filename
    (or path); stories without that metadata apply to the prompt set
    under evaluation.
    """
    evidence: dict[str, list[str]] = {}
    if not stories_dir.exists():
        return evidence

    prompt_name, allow_prompt_basename = _prompt_reference_scope(
        prompt_path, stories_dir
    )

    for story_path in sorted(stories_dir.rglob("story__*.md")):
        try:
            story_text = story_path.read_text(encoding="utf-8")
        except OSError as exc:
            if read_errors is not None:
                read_errors.append(f"{story_path.name}: {exc}")
            continue

        if not _story_links_prompt(
            story_text,
            prompt_name,
            allow_prompt_basename=allow_prompt_basename,
        ):
            continue

        covers_text = _extract_markdown_section(story_text, "Covers")
        if not covers_text:
            continue

        covers_prompt_name = (
            posixpath.basename(prompt_name)
            if allow_prompt_basename
            else prompt_name
        )
        rule_ids = _rule_ids_from_covers(covers_text, covers_prompt_name)
        for rid in rule_ids:
            evidence.setdefault(rid, [])
            if story_path.name not in evidence[rid]:
                evidence[rid].append(story_path.name)

    return evidence


def scan_story_validation_failures(
    stories_dir: Path,
    prompt_path: Path,
    read_errors: Optional[list[str]] = None,
) -> dict[str, list[str]]:
    """
    Return rule_id -> validation failure descriptions for linked stories.

    This is intentionally deterministic and uses the same story-linking rules
    as :func:`scan_story_evidence` (including metadata-less stories that apply
    to the prompt set). A linked story that claims rule coverage but has no
    ``## Acceptance Criteria`` section is considered failed coverage evidence.
    """
    failures: dict[str, list[str]] = {}
    if not stories_dir.exists():
        return failures

    prompt_name, allow_prompt_basename = _prompt_reference_scope(
        prompt_path, stories_dir
    )

    for story_path in sorted(stories_dir.rglob("story__*.md")):
        try:
            story_text = story_path.read_text(encoding="utf-8")
        except OSError as exc:
            if read_errors is not None:
                read_errors.append(f"{story_path.name}: {exc}")
            continue

        if not _story_links_prompt(
            story_text,
            prompt_name,
            allow_prompt_basename=allow_prompt_basename,
        ):
            continue

        covers_text = _extract_markdown_section(story_text, "Covers")
        if not covers_text:
            continue

        covers_prompt_name = (
            posixpath.basename(prompt_name)
            if allow_prompt_basename
            else prompt_name
        )
        rule_ids = _rule_ids_from_covers(covers_text, covers_prompt_name)
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


def _normalise_prompt_identity(value: str) -> str:
    """Return a stable, case-insensitive POSIX prompt identity."""
    normalised = posixpath.normpath(value.replace("\\", "/").strip())
    while normalised.startswith("./"):
        normalised = normalised[2:]
    return normalised.lower()


def _prompt_reference_scope(prompt_path: Path, tests_dir: Path) -> tuple[str, bool]:
    """Return project-relative identity and whether basename fallback is unique."""
    # Preserve the caller-visible lexical path (not a symlink-resolved path),
    # because prompt references use project identities such as ``prompts/x``.
    resolved_prompt = Path(os.path.abspath(prompt_path))
    resolved_tests = Path(os.path.abspath(tests_dir))
    common_root = Path(os.path.commonpath((resolved_prompt, resolved_tests)))
    identity = resolved_prompt.relative_to(common_root).as_posix()
    basename = resolved_prompt.name.lower()
    basename_matches = [
        candidate
        for candidate in common_root.rglob("*.prompt")
        if candidate.name.lower() == basename
    ]
    return _normalise_prompt_identity(identity), len(basename_matches) == 1


def _prompt_reference_matches(
    reference: str,
    prompt_identity: str,
    *,
    allow_basename: bool,
) -> bool:
    """Match an exact project-relative prompt ref, with safe legacy fallback."""
    normalised_ref = _normalise_prompt_identity(reference)
    normalised_target = _normalise_prompt_identity(prompt_identity)
    if normalised_ref == normalised_target:
        return True
    if not allow_basename:
        return False
    if "/" not in normalised_target:
        return posixpath.basename(normalised_ref) == normalised_target
    return (
        "/" not in normalised_ref
        and normalised_ref == posixpath.basename(normalised_target)
    )


def scan_test_evidence(
    tests_dir: Path,
    prompt_path: Optional[Path] = None,
    read_errors: Optional[list[str]] = None,
    require_prompt_qualified: bool = False,
) -> dict[str, list[str]]:
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

    prompt_name = ""
    allow_prompt_basename = False
    if prompt_path is not None:
        prompt_name, allow_prompt_basename = _prompt_reference_scope(
            prompt_path, tests_dir
        )

    for test_file in sorted(tests_dir.rglob("test_*.py")):
        try:
            source = test_file.read_text(encoding="utf-8")
        except OSError as exc:
            if read_errors is not None:
                read_errors.append(f"{test_file.name}: {exc}")
            continue

        _scan_test_file(
            source,
            evidence,
            prompt_name=prompt_name,
            require_prompt_qualified=require_prompt_qualified,
            allow_prompt_basename=allow_prompt_basename,
        )

    return evidence


def scan_test_validation_failures(
    tests_dir: Path,
    prompt_path: Optional[Path] = None,
    read_errors: Optional[list[str]] = None,
    require_prompt_qualified: bool = False,
) -> dict[str, list[str]]:
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

    prompt_name = ""
    allow_prompt_basename = False
    if prompt_path is not None:
        prompt_name, allow_prompt_basename = _prompt_reference_scope(
            prompt_path, tests_dir
        )

    for test_file in sorted(tests_dir.rglob("test_*.py")):
        try:
            source = test_file.read_text(encoding="utf-8")
        except OSError as exc:
            if read_errors is not None:
                read_errors.append(f"{test_file.name}: {exc}")
            continue

        try:
            with warnings.catch_warnings():
                warnings.simplefilter("ignore", SyntaxWarning)
                ast.parse(source)
        except SyntaxError as exc:
            referenced_rules = _rule_ids_from_test_source(
                source,
                prompt_name=prompt_name,
                require_prompt_qualified=require_prompt_qualified,
                allow_prompt_basename=allow_prompt_basename,
            )
            for rid in referenced_rules:
                failures.setdefault(rid, [])
                failures[rid].append(
                    f"{test_file.name}: syntax error on line {exc.lineno or '?'}"
                )

    return failures


def _rule_ids_from_test_source(
    source: str,
    *,
    prompt_name: str = "",
    require_prompt_qualified: bool = False,
    allow_prompt_basename: bool = True,
) -> set[str]:
    """Extract explicit rule IDs from a possibly invalid test file."""
    if require_prompt_qualified:
        evidence: dict[str, list[str]] = {}
        _scan_test_file_regex(
            source,
            evidence,
            prompt_name=prompt_name,
            require_prompt_qualified=True,
            allow_prompt_basename=allow_prompt_basename,
        )
        return set(evidence)

    ids: set[str] = set()
    for suffix in _TEST_FUNC_RE.findall(source):
        ids.add(f"R{suffix}".upper())
    for comment_match in _TEST_COMMENT_RE.finditer(source):
        ids.add(comment_match.group(1).upper())
    for ref_match in COVERAGE_REF_RE.finditer(source):
        ids.add(ref_match.group(1).upper())
    return ids


def _scan_test_file(  # pylint: disable=too-many-locals
    source: str,
    evidence: dict[str, list[str]],
    *,
    prompt_name: str,
    require_prompt_qualified: bool,
    allow_prompt_basename: bool = True,
) -> None:
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
        _scan_test_file_regex(
            source,
            evidence,
            prompt_name=prompt_name,
            require_prompt_qualified=require_prompt_qualified,
            allow_prompt_basename=allow_prompt_basename,
        )
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

        # Prompt-qualified mode: only accept references scoped to this prompt.
        if require_prompt_qualified:
            # Check the function docstring first line and the function signature line.
            docstring = ast.get_docstring(node) or ""
            first_line = docstring.splitlines()[0][:200] if docstring else ""
            sig_line = source.splitlines()[max(node.lineno - 1, 0)] if source else ""
            for text in (first_line, sig_line):
                for match in CROSS_MODULE_REF_RE.finditer(text):
                    if _prompt_reference_matches(
                        match.group(1),
                        prompt_name,
                        allow_basename=allow_prompt_basename,
                    ):
                        rid = match.group(2).upper()
                        evidence.setdefault(rid, [])
                        if fname not in evidence[rid]:
                            evidence[rid].append(fname)
            continue

        # Pattern 1: function name contains R<N>[a] (unqualified, single-prompt usage)
        for suffix in _TEST_FUNC_RE.findall(fname):
            rid = f"R{suffix}".upper()
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

        # Pattern 3: first line of docstring — requires explicit R<N>: or R<N> - form
        # to avoid false positives from bare mentions like "uses R1 algorithm"
        docstring = ast.get_docstring(node)
        if docstring:
            first_line = docstring.splitlines()[0][:120]
            for doc_match in _TEST_DOCSTRING_RE.finditer(first_line):
                rid = doc_match.group(1).upper()
                evidence.setdefault(rid, [])
                if fname not in evidence[rid]:
                    evidence[rid].append(fname)


def _scan_test_file_regex(
    source: str,
    evidence: dict[str, list[str]],
    *,
    prompt_name: str = "",
    require_prompt_qualified: bool = False,
    allow_prompt_basename: bool = True,
) -> None:
    """Fallback regex-only scanner used when AST parsing fails."""
    lines = source.splitlines()
    for line_index, line in enumerate(lines):
        stripped = line.strip()
        if not re.match(r"^(?:async\s+)?def\s+test", stripped):
            continue
        fname_match = re.match(r"(?:async\s+)?def\s+(test\w+)", stripped)
        if not fname_match:
            continue
        fname = fname_match.group(1)
        if require_prompt_qualified:
            # Mirror the AST path's bounded ownership surfaces: the signature
            # and the following line (where a one-line docstring normally sits).
            texts = [line]
            if line_index + 1 < len(lines):
                possible_docstring = lines[line_index + 1].lstrip()
                if re.match(r"^(?:[rRuU]{0,2})?(?:'''|\"\"\"|'|\")", possible_docstring):
                    texts.append(lines[line_index + 1])
            for text in texts:
                for match in CROSS_MODULE_REF_RE.finditer(text):
                    if _prompt_reference_matches(
                        match.group(1),
                        prompt_name,
                        allow_basename=allow_prompt_basename,
                    ):
                        rid = match.group(2).upper()
                        evidence.setdefault(rid, [])
                        if fname not in evidence[rid]:
                            evidence[rid].append(fname)
            continue
        for suffix in _TEST_FUNC_RE.findall(fname):
            rid = f"R{suffix}".upper()
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
    waiver_details: dict[str, tuple[str, str, Optional[str]]],
    story_evidence: dict[str, list[str]],
    test_evidence: dict[str, list[str]],
    validation_failures: Optional[dict[str, list[str]]] = None,
    *,
    waiver_id_to_rule: Optional[dict[str, str]] = None,
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
    waiver_status: Optional[str] = None
    waiver_expires: Optional[str] = None
    if waiver_ref:
        waiver_id = waiver_ref.group(1).upper()
        waived_rule = (waiver_id_to_rule or {}).get(waiver_id)
        if waived_rule is not None and waived_rule != rid:
            failures = list((validation_failures or {}).get(rid, []))
            failures.append(
                f"Waiver {waiver_id} waives {waived_rule}, not {rid}"
            )
            return RuleCoverage(
                rule_id=rid,
                status=STATUS_UNCHECKED,
                stories=list(story_evidence.get(rid, [])),
                tests=list(test_evidence.get(rid, [])),
                waiver=None,
                waiver_status=None,
                waiver_expires=None,
                failures=failures,
            )
        if rid in waiver_details:
            _, waiver_status, waiver_expires = waiver_details[rid]
        else:
            waiver_status = "untracked"
    elif rid in waiver_map:
        waiver_id = waiver_map[rid]
        if rid in waiver_details:
            _, waiver_status, waiver_expires = waiver_details[rid]

    if waiver_id:
        # Still collect any story evidence for display
        stories = story_evidence.get(rid, [])
        return RuleCoverage(
            rule_id=rid,
            status=STATUS_WAIVED,
            stories=stories,
            tests=[],
            waiver=waiver_id,
            waiver_status=waiver_status,
            waiver_expires=waiver_expires,
        )

    failures = list((validation_failures or {}).get(rid, []))
    if failures:
        return RuleCoverage(
            rule_id=rid,
            status=STATUS_FAILED,
            stories=list(story_evidence.get(rid, [])),
            tests=list(test_evidence.get(rid, [])),
            waiver=None,
            waiver_status=None,
            waiver_expires=None,
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

    has_story = bool(stories)
    has_test = bool(tests)

    if has_story and has_test:
        status = STATUS_CHECKED
    elif has_story:
        status = STATUS_STORY_ONLY
    elif has_test:
        status = STATUS_TEST_ONLY
    else:
        status = STATUS_UNCHECKED

    return RuleCoverage(
        rule_id=rid,
        status=status,
        stories=stories,
        tests=tests,
        waiver=None,
        waiver_status=None,
        waiver_expires=None,
    )

# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def _linked_story_ids(
    stories_dir: Path,
    prompt_path: Path,
    read_errors: Optional[list[str]] = None,
) -> list[str]:
    """Return the ``story_id`` of every story file that links to *prompt_path*.

    Uses the same linking rules as :func:`scan_story_evidence` (a story with
    ``<!-- pdd-story-prompts: ... -->`` must list the prompt; a metadata-less
    story applies to the prompt set). Result is sorted and de-duplicated.
    """
    from .story_regression import story_id  # local import: keeps pytest lazy

    if not stories_dir.exists():
        return []
    prompt_name, allow_prompt_basename = _prompt_reference_scope(
        prompt_path, stories_dir
    )
    ids: set[str] = set()
    for story_path in sorted(stories_dir.rglob("story__*.md")):
        try:
            story_text = story_path.read_text(encoding="utf-8")
        except OSError as exc:
            if read_errors is not None:
                read_errors.append(f"{story_path.name}: {exc}")
            continue
        if _story_links_prompt(
            story_text,
            prompt_name,
            allow_prompt_basename=allow_prompt_basename,
        ):
            ids.add(story_id(story_path))
    return sorted(ids)


def _story_slug_from_name(story_name: str) -> str:
    """Return ``<slug>`` for a ``story__<slug>.md`` filename."""
    if story_name.startswith("story__") and story_name.endswith(".md"):
        return story_name[len("story__"):-len(".md")]
    return Path(story_name).stem


def _cross_unit_story_partners(
    stories_dir: Path,
    prompt_path: Path,
    read_errors: Optional[list[str]] = None,
) -> dict[str, list[str]]:
    """Return linked cross-unit story filename -> all declared dev units."""
    if not stories_dir.exists():
        return {}

    from .user_story_tests import get_all_dev_units_for_story, story_is_cross_unit

    prompt_name, allow_prompt_basename = _prompt_reference_scope(
        prompt_path, stories_dir
    )
    partners: dict[str, list[str]] = {}
    for story_path in sorted(stories_dir.rglob("story__*.md")):
        try:
            story_text = story_path.read_text(encoding="utf-8")
        except OSError as exc:
            if read_errors is not None:
                read_errors.append(f"{story_path.name}: {exc}")
            continue
        if not _story_links_prompt(
            story_text,
            prompt_name,
            allow_prompt_basename=allow_prompt_basename,
        ):
            continue
        if not story_is_cross_unit(story_text):
            continue
        partners[story_path.name] = get_all_dev_units_for_story(story_text)
    return partners


def _story_evidence_for_status(
    story_evidence: dict[str, list[str]],
    cross_unit_partners: dict[str, list[str]],
    global_story_registry: Optional[set[str]],
) -> tuple[dict[str, list[str]], set[str]]:
    """Filter already-counted cross-unit stories out of status evidence."""
    if global_story_registry is None:
        return {rid: list(stories) for rid, stories in story_evidence.items()}, set()

    previously_counted = set(global_story_registry)
    newly_counted: set[str] = set()
    filtered: dict[str, list[str]] = {}

    for rid, stories in story_evidence.items():
        visible_for_status: list[str] = []
        for story_name in stories:
            if story_name not in cross_unit_partners:
                visible_for_status.append(story_name)
                continue
            slug = _story_slug_from_name(story_name)
            if slug in previously_counted:
                continue
            visible_for_status.append(story_name)
            newly_counted.add(slug)
        filtered[rid] = visible_for_status

    return filtered, newly_counted


def _annotate_cross_unit_rule(
    rule: RuleCoverage,
    cross_unit_partners: dict[str, list[str]],
) -> None:
    """Populate cross-unit fields on a rule based on its attributed stories."""
    partners: list[str] = []
    seen: set[str] = set()
    for story_name in rule.stories:
        for partner in cross_unit_partners.get(story_name, []):
            key = partner.lower()
            if key in seen:
                continue
            seen.add(key)
            partners.append(partner)
    if partners:
        rule.is_cross_unit = True
        rule.cross_unit_partners = partners


def build_coverage(
    path: Path,
    stories_dir: Optional[Path] = None,
    tests_dir: Optional[Path] = None,
    *,
    prompt_text: Optional[str] = None,
    require_prompt_qualified_tests: bool = False,
    story_map: "Optional[object]" = None,
    global_story_registry: Optional[set[str]] = None,
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

    if prompt_text is not None:
        text = prompt_text
    else:
        try:
            text = path.read_text(encoding="utf-8")
        except FileNotFoundError:
            result.error = f'File not found: "{path}"'
            return result
        except OSError as exc:
            result.error = str(exc)
            return result

    sections = _extract_sections(text)

    if "contract_rules" not in sections:
        # Legacy prompt — no <contract_rules> tag at all
        return result

    result.has_contract_rules = True
    rules_text = sections["contract_rules"]
    if not rules_text.strip():
        # Section tag present but empty — has contracts, zero rules
        return result
    rule_ids = _parse_rule_ids(rules_text)

    coverage_text = sections.get("coverage", "")
    coverage_entries = _parse_coverage_block(coverage_text) if coverage_text else {}

    waivers_text = sections.get("waivers", "")
    waiver_map = _parse_waiver_rule_map(waivers_text) if waivers_text else {}
    extracted_waivers = _extract_waivers(waivers_text) if waivers_text else []
    waiver_id_to_rule = waiver_id_to_rule_map(extracted_waivers)
    waiver_details: dict[str, tuple[str, str, Optional[str]]] = {}
    if waivers_text:
        for waiver in extracted_waivers:
            if not waiver.rule_id:
                continue
            status = classify_waiver_status(waiver, set(rule_ids))
            waiver_details[waiver.rule_id.upper()] = (
                waiver.raw_id,
                status,
                waiver.expires.isoformat() if waiver.expires else None,
            )

    read_errors: list[str] = []
    story_evidence = scan_story_evidence(stories_dir, path, read_errors=read_errors)
    cross_unit_partners = _cross_unit_story_partners(stories_dir, path, read_errors=read_errors)
    result.cross_unit_stories = sorted(cross_unit_partners)
    story_evidence_for_status, newly_counted_cross_unit = _story_evidence_for_status(
        story_evidence,
        cross_unit_partners,
        global_story_registry,
    )
    test_evidence = scan_test_evidence(
        tests_dir,
        prompt_path=path,
        read_errors=read_errors,
        require_prompt_qualified=require_prompt_qualified_tests,
    )
    validation_failures: dict[str, list[str]] = {}
    for source in (
        scan_story_validation_failures(stories_dir, path, read_errors=read_errors),
        scan_test_validation_failures(
            tests_dir,
            prompt_path=path,
            read_errors=read_errors,
            require_prompt_qualified=require_prompt_qualified_tests,
        ),
    ):
        for rid, messages in source.items():
            validation_failures.setdefault(rid, []).extend(messages)
    result.read_errors = read_errors

    for rid in rule_ids:
        rule_cov = _classify_rule(
            rid,
            coverage_entries,
            waiver_map,
            waiver_details,
            story_evidence_for_status,
            test_evidence,
            validation_failures,
            waiver_id_to_rule=waiver_id_to_rule,
        )
        attributed_stories = list(story_evidence.get(rid, []))
        for story_name in attributed_stories:
            if story_name not in rule_cov.stories:
                rule_cov.stories.append(story_name)
        _annotate_cross_unit_rule(rule_cov, cross_unit_partners)
        result.rules.append(rule_cov)

    if global_story_registry is not None:
        global_story_registry.update(newly_counted_cross_unit)

    _attach_story_regression(result, path, stories_dir, tests_dir, story_map)

    return result


def _attach_story_regression(
    result: CoverageResult,
    path: Path,
    stories_dir: Path,
    tests_dir: Path,
    story_map: "Optional[object]",
) -> None:
    """Fill the orthogonal per-story ``has_regression_test`` dimension.

    Queries the ``story_regression`` traceability API rather than re-implementing
    pytest collection here. The story<->test map is built once (lazily) and may
    be supplied by the caller (``build_coverage_directory``) so a directory scan
    does not re-collect per prompt.
    """
    linked = _linked_story_ids(stories_dir, path, read_errors=result.read_errors)
    if not linked and story_map is None:
        return  # nothing story-linked here and no shared map — stay cheap

    from .story_regression import (  # local import keeps pytest lazy
        StoryTestMap,
        build_story_map,
        discover_story_ids,
    )
    from .story_regression_gate import evaluate_story_regression
    from .user_story_tests import story_id as story_id_from_path

    smap: StoryTestMap = story_map if story_map is not None else build_story_map(tests_dir)

    story_lookup = {
        sid: story_path
        for story_path in sorted(stories_dir.rglob("story__*.md"))
        for sid in [story_id_from_path(story_path)]
    }
    for sid in linked:
        story_path = story_lookup.get(sid)
        if story_path is None:
            result.stories.append(
                StoryRegression(
                    sid,
                    smap.has_regression_test(sid),
                    "story-regression-missing",
                )
            )
            continue
        gate = evaluate_story_regression(story_path, tests_dir=tests_dir, story_map=smap)
        result.stories.append(
            StoryRegression(
                sid,
                gate.has_regression_test,
                gate.status,
                gate.tests,
                gate.current_hash,
            )
        )

    # Validation-warning orphan direction: a marker names a story_id that has no
    # ``story__<slug>.md`` on disk. Distinct from the "story has no test" gap.
    on_disk = discover_story_ids(str(stories_dir))
    for sid in sorted(smap.referenced_story_ids - on_disk):
        result.regression_warnings.append(
            f"@pytest.mark.story(story_id={sid!r}) references a story with no "
            f"story__{sid}.md on disk"
        )


def build_coverage_directory(
    directory: Path,
    stories_dir: Optional[Path] = None,
    tests_dir: Optional[Path] = None,
) -> list[CoverageResult]:
    """
    Build coverage matrices for every `*.prompt` file under a directory.

    Returns one CoverageResult per file, skipping `*_llm.prompt` files.
    """
    # Build the story<->test map ONCE for the whole directory scan so we do not
    # re-run pytest collection per prompt.
    from .story_regression import build_story_map  # local import keeps pytest lazy

    shared_story_map = build_story_map(tests_dir if tests_dir is not None else Path("tests"))
    global_story_registry: set[str] = set()

    results: list[CoverageResult] = []
    for prompt_path in sorted(directory.rglob("*.prompt")):
        if prompt_path.name.lower().endswith("_llm.prompt"):
            continue
        # Directory mode must avoid cross-prompt test evidence false positives.
        # Require prompt-qualified test references (e.g. foo_python.prompt#R1).
        results.append(
            build_coverage(
                prompt_path,
                stories_dir,
                tests_dir,
                require_prompt_qualified_tests=True,
                story_map=shared_story_map,
                global_story_registry=global_story_registry,
            )
        )
    return results
