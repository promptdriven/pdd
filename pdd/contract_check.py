# pylint: disable=too-many-lines,duplicate-code
"""
Contract authoring check engine.

Parses <contract_rules>, <vocabulary>, <capabilities>, <coverage>, <waivers>,
and <non_responsibilities> sections and reports structural authoring defects
without requiring an LLM.

Public API
----------
check_prompt(path, *, strict=False) -> ContractResult
check_directory(directory, *, strict=False) -> list[ContractResult]
check_stories(stories_dir, prompts_dir, *, strict=False) -> list[ContractResult]
run_llm_ambiguity_pass(path, strength, temperature, time, verbose) -> list[ContractIssue]
"""
from __future__ import annotations

import json
import logging
import re
from dataclasses import dataclass, field
from datetime import date
from pathlib import Path
from typing import Optional

from .contract_ir import (
    PromptContractIR,
    Rule,
    Waiver,
    extract_rules as _extract_rules,
    extract_sections as _extract_sections,
    extract_waivers as _extract_waivers,
    parse_prompt_contracts,
)
from .prompt_lint import VAGUE_TERMS

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Modal verbs required in every rule / capability line
# ---------------------------------------------------------------------------

MODALS: frozenset[str] = frozenset({
    "MUST NOT",
    "MUST",
    "MAY NOT",
    "MAY",
    "SHOULD NOT",
    "SHOULD",
    "DOES NOT",
    "SHALL NOT",
    "SHALL",
})

# Ordered longest-first so "MUST NOT" matches before "MUST"
_MODAL_PATTERN = re.compile(
    r"\b(" + "|".join(re.escape(m) for m in sorted(MODALS, key=len, reverse=True)) + r")\b",
)

# ---------------------------------------------------------------------------
# Rule ID patterns (shared with coverage_contracts via contract_ir)
# ---------------------------------------------------------------------------

from .contract_ir import (  # noqa: E402  (regex aliases co-located with parsers)
    COVERAGE_REF_RE as _COVERAGE_REF_RE,
    CROSS_MODULE_REF_RE as _CROSS_MODULE_REF_RE,
    iter_covers_refs,
)

# Canonical explicit IDs (both R1 and R-001 forms supported):
#   R1  R-1  R-001  RULE1  RULE-001
_EXPLICIT_ID_RE = re.compile(r"^(R-?\d+|RULE-?\d+)\b", re.IGNORECASE)

# Candidate "looks like an ID" but malformed:  RR-01  R_001  RULE_003
_CANDIDATE_ID_RE = re.compile(r"^([A-Z]{1,5}[-_]\w+)\b", re.IGNORECASE)

# Sequential number prefix:  1.  2)  3:
_SEQ_ID_RE = re.compile(r"^(\d+)[.):\s]")

# Waiver ID: W1  W-1  W01
_WAIVER_ID_RE = re.compile(r"^(W-?\d+):", re.IGNORECASE)
_WAIVER_REF_RE = re.compile(r"\bWAIVED\s+(W-?\d+)\b", re.IGNORECASE)

# ---------------------------------------------------------------------------
# Data classes (Rule/Waiver live in contract_ir)
# ---------------------------------------------------------------------------


@dataclass
class ContractIssue:  # pylint: disable=too-many-instance-attributes
    """A single contract-check finding."""

    level: str       # "warn" | "error"
    code: str        # e.g. "DUPLICATE_ID", "MISSING_MODAL"
    rule_id: str     # e.g. "R1" or "" if not rule-specific
    section: str     # e.g. "contract_rules", "coverage"
    line: str        # verbatim source line (or first line of block)
    message: str
    term: str = ""   # matched vague term (populated for VAGUE_TERM issues)
    suggestion: str = ""
    interpretations: list[str] = field(default_factory=list)

    def as_dict(self) -> dict:
        """Serialise this issue to a JSON-safe dictionary."""
        return {
            "level": self.level,
            "code": self.code,
            "rule_id": self.rule_id,
            "section": self.section,
            "line": self.line,
            "message": self.message,
            "term": self.term,
            "suggestion": self.suggestion,
            "interpretations": self.interpretations,
        }


@dataclass
class ContractResult:
    """Aggregated check findings for one file."""

    path: Path
    issues: list[ContractIssue] = field(default_factory=list)

    @property
    def warn_count(self) -> int:
        """Count of warning-level issues."""
        return sum(1 for i in self.issues if i.level == "warn")

    @property
    def error_count(self) -> int:
        """Count of error-level issues."""
        return sum(1 for i in self.issues if i.level == "error")

    def as_dict(self) -> dict:
        """Serialise this result to a JSON-safe dictionary."""
        return {
            "path": str(self.path),
            "warn_count": self.warn_count,
            "error_count": self.error_count,
            "issues": [i.as_dict() for i in self.issues],
        }


# ---------------------------------------------------------------------------
# Individual check functions
# ---------------------------------------------------------------------------

def _check_duplicate_ids(rules: list[Rule]) -> list[ContractIssue]:
    """Emit DUPLICATE_ID error when the same ID appears more than once."""
    issues: list[ContractIssue] = []
    seen: dict[str, int] = {}
    for rule in rules:
        rid = rule.raw_id
        if rid == "(unnumbered)":
            continue
        if rid in seen:
            issues.append(ContractIssue(
                level="error",
                code="DUPLICATE_ID",
                rule_id=rid,
                section="contract_rules",
                line=rule.line,
                message=f'Rule ID "{rid}" appears more than once in <contract_rules>.',
                suggestion="Assign a unique ID to each rule. Rename or remove the duplicate.",
            ))
        else:
            seen[rid] = 1
    return issues


def _check_malformed_ids(rules_text: str) -> list[ContractIssue]:
    """
    Emit MALFORMED_ID error for lines that start with something that looks like
    an ID prefix but does not match any canonical form.
    """
    issues: list[ContractIssue] = []
    for line in rules_text.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        # Skip lines that are already valid
        if _EXPLICIT_ID_RE.match(stripped) or _SEQ_ID_RE.match(stripped):
            continue
        if stripped.startswith(("-", "*", "•")):
            continue
        # Check for candidate malformed prefixes: RR-01, R_001, RULE_1
        cand = _CANDIDATE_ID_RE.match(stripped)
        if cand:
            raw = cand.group(1)
            if not _EXPLICIT_ID_RE.match(stripped):
                issues.append(ContractIssue(
                    level="error",
                    code="MALFORMED_ID",
                    rule_id=raw,
                    section="contract_rules",
                    line=stripped,
                    message=(
                        f'Rule prefix "{raw}" does not match the canonical ID format. '
                        f'Use "R1 -", "R1:", "R-001:", … or plain "1.", "2." sequential numbering.'
                    ),
                    suggestion='Rename to "R<N> - Short name" or use sequential numbering.',
                ))
    return issues


def _check_sequential_ids(rules: list[Rule]) -> list[ContractIssue]:
    """
    Warn (not error) when explicit R<N> IDs have a numeric gap.
    Only applies when rules use consistent explicit IDs.
    """
    issues: list[ContractIssue] = []
    explicit_rules = [r for r in rules if r.raw_id not in ("(unnumbered)",)
                      and r.num is not None]
    if not explicit_rules:
        return issues

    nums = sorted(set(r.num for r in explicit_rules if r.num is not None))
    for i in range(1, len(nums)):
        if nums[i] != nums[i - 1] + 1:
            issues.append(ContractIssue(
                level="warn",
                code="NON_SEQUENTIAL_ID",
                rule_id=f"R{nums[i]}",
                section="contract_rules",
                line="",
                message=(
                    f"Rule IDs jump from {nums[i-1]} to {nums[i]}; "
                    f"one or more IDs may have been deleted or misnumbered."
                ),
                suggestion="Renumber rules sequentially or add a comment explaining the gap.",
            ))
    return issues


def _check_missing_modal(rules: list[Rule], *, strict: bool) -> list[ContractIssue]:
    """Emit MISSING_MODAL for rules that lack a recognised modal verb."""
    issues: list[ContractIssue] = []
    for rule in rules:
        if rule.modal:
            continue
        if rule.raw_id == "(unnumbered)" and not rule.line.lstrip("-* "):
            continue
        level = "error" if strict else "warn"
        issues.append(ContractIssue(
            level=level,
            code="MISSING_MODAL",
            rule_id=rule.raw_id,
            section="contract_rules",
            line=rule.line,
            message=(
                f'Rule [{rule.raw_id}] has no modal verb '
                f'(MUST / MUST NOT / MAY / SHOULD / DOES NOT).'
            ),
            suggestion='Add a modal verb: "The system MUST …" or "The service MUST NOT …".',
        ))
    return issues


def _check_vague_terms(
    rules_text: str,
    vocab_terms: set[str],
) -> list[ContractIssue]:
    """
    Warn when a rule line uses a known vague phrase not covered by <vocabulary>.
    Reuses the VAGUE_TERMS frozenset and vocabulary suppression from prompt_lint.
    """
    issues: list[ContractIssue] = []
    _vague_pat = re.compile(
        r"\b(" + "|".join(re.escape(t) for t in sorted(VAGUE_TERMS)) + r")\b",
        re.IGNORECASE,
    )
    for line in rules_text.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        matches = {m.lower() for m in _vague_pat.findall(stripped)}
        undefined = matches - vocab_terms
        for term in sorted(undefined):
            issues.append(ContractIssue(
                level="warn",
                code="VAGUE_TERM",
                rule_id="",
                section="contract_rules",
                line=stripped,
                message=(
                    f'Vague term "{term}" used in <contract_rules> without a '
                    f"<vocabulary> definition."
                ),
                term=term,
                suggestion=f"{term}: <add a precise, observable definition here>",
            ))
    return issues


def _check_coverage_entries(
    coverage_text: str,
    known_ids: set[str],
    known_waiver_ids: set[str],
) -> list[ContractIssue]:
    """
    Validate <coverage> entries. Three entry types are recognised:

        R1: story__refund_invalid_amount.md   → validate ID exists
        R4: TODO add idempotency story        → UNCHECKED_RULE warn
        R6: WAIVED W1                         → validate W1 in <waivers>
    """
    issues: list[ContractIssue] = []
    for line in coverage_text.splitlines():
        stripped = line.strip()
        if not stripped:
            continue

        # Find the leading rule ID (may or may not be present)
        id_match = _COVERAGE_REF_RE.match(stripped.lstrip("-* "))
        if not id_match:
            continue
        ref_id = id_match.group(1).upper()

        # Everything after the first ":" is the evidence text
        colon_pos = stripped.find(":")
        evidence = stripped[colon_pos + 1:].strip() if colon_pos != -1 else ""

        # Unknown rule ID
        if ref_id not in known_ids:
            issues.append(ContractIssue(
                level="error",
                code="UNKNOWN_COVERAGE_REF",
                rule_id=ref_id,
                section="coverage",
                line=stripped,
                message=(
                    f'<coverage> references rule ID "{ref_id}" which does not '
                    f"exist in <contract_rules>."
                ),
                suggestion=(
                    f"Add a rule with ID {ref_id} to <contract_rules>, or remove "
                    f"this coverage entry."
                ),
            ))
            continue

        # Coverage placeholder: evidence text begins with "TODO"
        if evidence.upper().startswith("TODO"):
            issues.append(ContractIssue(
                level="warn",
                code="UNCHECKED_RULE",
                rule_id=ref_id,
                section="coverage",
                line=stripped,
                message=(
                    f'Rule [{ref_id}] coverage is marked TODO. '
                    f"Add a story, test, or waiver before production use."
                ),
                suggestion=(
                    "Replace 'TODO' with: a story filename, an executable test name, "
                    "or 'WAIVED W<N>' with a corresponding <waivers> entry."
                ),
            ))
            continue

        # WAIVED entry — cross-reference against <waivers>
        waived_match = _WAIVER_REF_RE.search(evidence)
        if waived_match:
            waiver_id = waived_match.group(1).upper()
            if waiver_id not in known_waiver_ids:
                issues.append(ContractIssue(
                    level="error",
                    code="WAIVER_REF_MISSING",
                    rule_id=ref_id,
                    section="coverage",
                    line=stripped,
                    message=(
                        f'Coverage for rule [{ref_id}] cites waiver "{waiver_id}" '
                        f"which has no corresponding entry in <waivers>."
                    ),
                    suggestion=(
                        f"Add a W{waiver_id.lstrip('W').lstrip('-')} block to <waivers>, "
                        f"or remove the WAIVED reference."
                    ),
                ))

    return issues


def _check_must_not_coverage(
    rules: list[Rule],
    coverage_text: str,
) -> list[ContractIssue]:
    """
    Warn when a MUST NOT rule has no evidence in <coverage>.
    Only fires when a <coverage> section is present at all.
    """
    issues: list[ContractIssue] = []
    covered_ids: set[str] = set()
    for coverage_match in _COVERAGE_REF_RE.finditer(coverage_text):
        covered_ids.add(coverage_match.group(1).upper())

    for rule in rules:
        if not rule.is_must_not:
            continue
        rid = rule.raw_id
        if rid == "(unnumbered)":
            continue
        if rid.upper() not in covered_ids:
            issues.append(ContractIssue(
                level="warn",
                code="UNCOVERED_MUST_NOT",
                rule_id=rid,
                section="contract_rules",
                line=rule.line,
                message=(
                    f'High-risk rule [{rid}] uses MUST NOT but has no entry in '
                    f"<coverage>. Add a test, story, or waiver reference."
                ),
                suggestion=(
                    f"In <coverage>, add: {rid}: <test name, story filename, or WAIVED W<N>>"
                ),
            ))
    return issues


def _check_waivers(waivers_text: str) -> list[ContractIssue]:
    """
    Validate <waivers> blocks:
      - MISSING_WAIVER_FIELDS warn: missing Rule, Reason, Approved by, or Expires
      - EXPIRED_WAIVER warn: Expires date is in the past
    """
    issues: list[ContractIssue] = []
    required_fields = ("rule", "reason", "approved by", "expires")

    for waiver in _extract_waivers(waivers_text):
        # Check required fields
        fields_present = {
            "rule": bool(waiver.rule_id),
            "reason": bool(waiver.reason),
            "approved by": bool(waiver.approved_by),
            "expires": bool(waiver.expires is not None or
                            re.search(r"expires\s*:", waiver.raw_block, re.IGNORECASE)),
        }
        missing = [f for f in required_fields if not fields_present.get(f, False)]
        if missing:
            issues.append(ContractIssue(
                level="warn",
                code="MISSING_WAIVER_FIELDS",
                rule_id=waiver.raw_id,
                section="waivers",
                line=f"{waiver.raw_id}:",
                message=(
                    f'Waiver [{waiver.raw_id}] is missing required fields: '
                    f'{", ".join(missing)}.'
                ),
                suggestion=(
                    "Add all required fields: Rule, Reason, Approved by, Expires."
                ),
            ))

        # Check expiry
        if waiver.expires is not None and waiver.expires < date.today():
            issues.append(ContractIssue(
                level="warn",
                code="EXPIRED_WAIVER",
                rule_id=waiver.raw_id,
                section="waivers",
                line=f"Expires: {waiver.expires.isoformat()}",
                message=(
                    f'Waiver [{waiver.raw_id}] for rule [{waiver.rule_id}] expired on '
                    f"{waiver.expires.isoformat()}."
                ),
                suggestion=(
                    "Extend the waiver expiry date, add a story/test to close it, "
                    "or remove the waiver if the rule is now covered."
                ),
            ))

    return issues


def _check_capabilities_modals(capabilities_text: str) -> list[ContractIssue]:
    """
    Emit MISSING_MODAL warn for <capabilities> lines that lack a modal verb.
    Capability lines should use MAY / MUST NOT / MUST / SHOULD.
    Comment/blank lines and lines starting with '#' are skipped.
    """
    issues: list[ContractIssue] = []
    for line in capabilities_text.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if not _MODAL_PATTERN.search(stripped):
            issues.append(ContractIssue(
                level="warn",
                code="MISSING_MODAL",
                rule_id="",
                section="capabilities",
                line=stripped,
                message=(
                    f'Capability line has no modal verb (MAY / MUST NOT / MUST / SHOULD): '
                    f'"{stripped[:80]}"'
                ),
                suggestion='Use a modal: "- MAY read …", "- MUST NOT call …".',
            ))
    return issues


def _check_non_responsibilities_modals(non_resp_text: str) -> list[ContractIssue]:
    """
    Emit MISSING_MODAL warn for <non_responsibilities> lines that lack a modal verb.

    Non-responsibility lines should use DOES NOT / MUST NOT / MAY NOT to make
    the exclusion explicit rather than just stating scope informally.
    Comment/blank lines and lines starting with '#' are skipped.
    """
    issues: list[ContractIssue] = []
    for line in non_resp_text.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if not _MODAL_PATTERN.search(stripped):
            issues.append(ContractIssue(
                level="warn",
                code="MISSING_MODAL",
                rule_id="",
                section="non_responsibilities",
                line=stripped,
                message=(
                    f'Non-responsibility line has no modal verb '
                    f'(DOES NOT / MUST NOT / MAY NOT / WILL NOT): '
                    f'"{stripped[:80]}"'
                ),
                suggestion=(
                    'Use an explicit modal: "- DOES NOT handle …", '
                    '"- MUST NOT be called for …".'
                ),
            ))
    return issues


def _check_story_covers(
    story_text: str,
    linked_prompt_rules: Optional[dict[str, set[str]]],
) -> list[ContractIssue]:
    """
    Check ## Covers entries in a user story.

    Handles both formats from the prompting guide:
      Single-prompt:    - R1: rule name
      Cross-module:     - prompts/foo.prompt#R3: rule name

    If linked_prompt_rules is provided (maps prompt filename → set of known IDs),
    also verify that referenced IDs exist in the linked prompt.
    """
    issues: list[ContractIssue] = []
    sections = _extract_sections(story_text)
    covers_text = sections.get("covers", "")
    if not covers_text or linked_prompt_rules is None:
        return issues

    for ref in iter_covers_refs(covers_text):
        if ref.prompt_filename is not None:
            prompt_file = ref.prompt_filename
            prompt_ids = linked_prompt_rules.get(prompt_file, set())
            if not prompt_ids:
                prompt_ids = next(
                    (ids for k, ids in linked_prompt_rules.items()
                     if k.endswith(prompt_file)),
                    set(),
                )
            if prompt_ids and ref.rule_id not in prompt_ids:
                issues.append(ContractIssue(
                    level="warn",
                    code="UNKNOWN_STORY_REF",
                    rule_id=ref.rule_id,
                    section="covers",
                    line=ref.line,
                    message=(
                        f'Story ## Covers references rule ID "{ref.rule_id}" in '
                        f'"{prompt_file}" which was not found in that prompt\'s '
                        f"<contract_rules>."
                    ),
                    suggestion=(
                        f"Add rule {ref.rule_id} to {prompt_file}'s <contract_rules>, "
                        f"or remove this ## Covers entry."
                    ),
                ))
        else:
            found_in_any = any(
                ref.rule_id in ids for ids in linked_prompt_rules.values()
            )
            if not found_in_any:
                issues.append(ContractIssue(
                    level="warn",
                    code="UNKNOWN_STORY_REF",
                    rule_id=ref.rule_id,
                    section="covers",
                    line=ref.line,
                    message=(
                        f'Story ## Covers references rule ID "{ref.rule_id}" which was '
                        f"not found in any linked prompt's <contract_rules>."
                    ),
                    suggestion=(
                        f"Add rule {ref.rule_id} to the linked prompt's <contract_rules>, "
                        f"or remove this ## Covers entry."
                    ),
                ))

    return issues


# ---------------------------------------------------------------------------
# Top-level check functions
# ---------------------------------------------------------------------------

def _check_unknown_test_refs(
    coverage_text: str,
    known_ids: set[str],
    prompt_path: Path,
) -> list[ContractIssue]:
    """
    Warn when <coverage> cites a test file path that does not exist.
    """
    issues: list[ContractIssue] = []
    for line in coverage_text.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        id_match = _COVERAGE_REF_RE.match(stripped.lstrip("-* "))
        if not id_match:
            continue
        ref_id = id_match.group(1).upper()
        if ref_id not in known_ids:
            continue
        colon_pos = stripped.find(":")
        evidence = stripped[colon_pos + 1:].strip() if colon_pos != -1 else ""
        if not evidence or evidence.upper().startswith("TODO"):
            continue
        if _WAIVER_REF_RE.search(evidence):
            continue
        for part in [p.strip() for p in evidence.split(",")]:
            if not part.lower().endswith(".py"):
                continue
            candidate = Path(part)
            if candidate.is_absolute():
                if not candidate.exists():
                    issues.append(ContractIssue(
                        level="warn",
                        code="UNKNOWN_TEST_REF",
                        rule_id=ref_id,
                        section="coverage",
                        line=stripped,
                        message=f'<coverage> test path "{part}" was not found.',
                        suggestion="Fix the path or add the test file.",
                    ))
                continue
            found = False
            for base in (prompt_path.parent, Path.cwd(), Path("tests")):
                if (base / candidate).exists() or (base / part).exists():
                    found = True
                    break
            if not found and not (Path("tests") / candidate.name).exists():
                issues.append(ContractIssue(
                    level="warn",
                    code="UNKNOWN_TEST_REF",
                    rule_id=ref_id,
                    section="coverage",
                    line=stripped,
                    message=f'<coverage> test path "{part}" was not found.',
                    suggestion="Fix the path or add the test file.",
                ))
    return issues


def check_prompt_from_ir(ir: PromptContractIR, *, strict: bool = False) -> ContractResult:  # pylint: disable=too-many-locals
    """Run deterministic checks on a parsed PromptContractIR."""
    result = ContractResult(path=ir.path)

    if ir.parse_error:
        result.issues.append(ContractIssue(
            level="error",
            code="FILE_NOT_FOUND" if "not found" in ir.parse_error.lower() else "PARSE_ERROR",
            rule_id="",
            section="",
            line="",
            message=ir.parse_error,
        ))
        return result

    if not ir.has_contract_sections:
        return result

    rules = ir.rules
    rules_text = ir.sections.get("contract_rules", "")
    coverage_text = ir.sections.get("coverage", "")
    waivers_text = ir.sections.get("waivers", "")
    capabilities_text = ir.sections.get("capabilities", "")
    non_resp_text = ir.sections.get("non_responsibilities", "")
    known_ids = ir.known_rule_ids
    known_waiver_ids = ir.known_waiver_ids

    if rules_text:
        result.issues.extend(_check_duplicate_ids(rules))
        result.issues.extend(_check_malformed_ids(rules_text))
        result.issues.extend(_check_sequential_ids(rules))
        result.issues.extend(_check_missing_modal(rules, strict=strict))
        result.issues.extend(_check_vague_terms(rules_text, ir.vocabulary_terms))

    if coverage_text:
        result.issues.extend(
            _check_coverage_entries(coverage_text, known_ids, known_waiver_ids)
        )
        result.issues.extend(_check_must_not_coverage(rules, coverage_text))
        result.issues.extend(
            _check_unknown_test_refs(coverage_text, known_ids, ir.path)
        )

    if waivers_text:
        result.issues.extend(_check_waivers(waivers_text))

    if capabilities_text:
        result.issues.extend(_check_capabilities_modals(capabilities_text))

    if non_resp_text:
        result.issues.extend(_check_non_responsibilities_modals(non_resp_text))

    if strict:
        for issue in result.issues:
            issue.level = "error"

    return result


def check_prompt(path: Path, *, strict: bool = False) -> ContractResult:
    """
    Run all deterministic checks on a single prompt file.

    Returns a ContractResult with zero issues for prompts that have no
    contract sections (legacy prompts without structure are never hard-failed).
    """
    ir = parse_prompt_contracts(path)
    return check_prompt_from_ir(ir, strict=strict)


def check_directory(directory: Path, *, strict: bool = False) -> list[ContractResult]:
    """Run check_prompt on every *.prompt file under a directory (recursive)."""
    results: list[ContractResult] = []
    for prompt_path in sorted(directory.rglob("*.prompt")):
        results.append(check_prompt(prompt_path, strict=strict))
    return results


def check_stories(  # pylint: disable=too-many-locals
    stories_dir: Path,
    prompts_dir: Optional[Path] = None,
    *,
    strict: bool = False,
) -> list[ContractResult]:
    """
    Check story__*.md files for ## Covers rule-ID validity.

    If prompts_dir is provided, cross-references IDs against the prompt files
    named in the story's <!-- pdd-story-prompts: … --> metadata comment.
    """
    results: list[ContractResult] = []
    if not stories_dir.exists():
        return results

    # Build prompt ID map if prompts_dir given
    prompt_id_map: dict[str, set[str]] = {}
    if prompts_dir and prompts_dir.exists():
        for prompt_path in prompts_dir.rglob("*.prompt"):
            try:
                ir = parse_prompt_contracts(prompt_path)
                if ir.has_contract_rules:
                    prompt_id_map[prompt_path.name] = ir.known_rule_ids
            except Exception:  # noqa: BLE001  # pylint: disable=broad-exception-caught
                pass

    for story_path in sorted(stories_dir.rglob("story__*.md")):
        result = ContractResult(path=story_path)
        try:
            story_text = story_path.read_text(encoding="utf-8")
        except Exception:  # noqa: BLE001  # pylint: disable=broad-exception-caught
            continue

        linked: Optional[dict[str, set[str]]] = None
        if prompt_id_map:
            # Look for <!-- pdd-story-prompts: foo.prompt, bar.prompt -->
            meta_match = re.search(
                r"<!--\s*pdd-story-prompts:\s*([^>]+)-->", story_text
            )
            if meta_match:
                names = [n.strip() for n in meta_match.group(1).split(",")]
                linked = {n: prompt_id_map.get(n, set()) for n in names}
            else:
                linked = prompt_id_map  # check against all known prompts

        issues = _check_story_covers(story_text, linked)
        if strict:
            for issue in issues:
                issue.level = "error"
        result.issues.extend(issues)
        results.append(result)

    return results


# ---------------------------------------------------------------------------
# Optional LLM ambiguity pass
# ---------------------------------------------------------------------------

def run_llm_ambiguity_pass(  # pylint: disable=too-many-locals
    path: Path,
    strength: float = 0.5,
    temperature: float = 0.0,
    time: Optional[float] = None,
    verbose: bool = False,
) -> list[ContractIssue]:
    """
    Run an LLM review of ambiguous terms in <contract_rules> and suggest
    <vocabulary> definitions.

    This is a best-effort enhancement; failures are logged and an empty list
    is returned so that CI is never blocked.
    """
    try:
        from .llm_invoke import llm_invoke  # pylint: disable=import-outside-toplevel
        from .preprocess import preprocess  # pylint: disable=import-outside-toplevel
    except ImportError:
        logger.warning("LLM dependencies not available; skipping ambiguity pass.")
        return []

    try:
        text = path.read_text(encoding="utf-8")
        sections = _extract_sections(text)
        rules_text = sections.get("contract_rules", "")
        if not rules_text:
            return []

        # Build a list of vague terms actually present
        _vague_pat = re.compile(
            r"\b(" + "|".join(re.escape(t) for t in sorted(VAGUE_TERMS)) + r")\b",
            re.IGNORECASE,
        )
        found_terms = sorted({m.lower() for m in _vague_pat.findall(rules_text)})
        if not found_terms:
            return []

        prompt_template_path = (
            Path(__file__).parent / "prompts" / "contract_check_LLM.prompt"
        )
        template = prompt_template_path.read_text(encoding="utf-8")
        filled = template.replace("{contract_content}", rules_text).replace(
            "{vague_terms_list}", ", ".join(found_terms)
        )
        filled = preprocess(filled, recursive=False, double_curly_brackets=False)

        result = llm_invoke(
            messages=[{"role": "user", "content": filled}],
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose,
        )
        data = json.loads(result["result"])
        issues: list[ContractIssue] = []
        for entry in data:
            issues.append(ContractIssue(
                level="warn",
                code="LLM_AMBIGUITY",
                rule_id="",
                section="llm",
                line="",
                message=f'LLM flagged "{entry.get("term", "")}" as potentially ambiguous.',
                suggestion=entry.get("suggestion", ""),
                interpretations=entry.get("interpretations", []),
            ))
        return issues
    except Exception as exc:  # noqa: BLE001  # pylint: disable=broad-exception-caught
        logger.warning("LLM ambiguity pass failed: %s", exc)
        return []
