"""
Deterministic formalization-readiness checks for prompt contract IR.

Used by ``scan_prompt`` and as gates before LLM formalize write-back.
"""
from __future__ import annotations

import re
from typing import TYPE_CHECKING

from .prompt_lint import LintIssue

if TYPE_CHECKING:
    from .contract_ir import FormalizationRecord, PromptContractIR

_FORMAL_TEST_KEYWORDS = re.compile(
    r"\b(z3|smt|formal|proof|bounded)\b",
    re.IGNORECASE,
)
_PREDICATE_VAR_RE = re.compile(r"\b([a-z_][a-z0-9_]*)\b", re.IGNORECASE)
_PREDICATE_KEYWORDS = frozenset({
    "true", "false", "and", "or", "not", "implies", "if", "then", "else",
    "forall", "exists", "int", "bool", "str", "real", "when", "must",
})


def check_formalization(ir: "PromptContractIR", *, strict: bool = False) -> list[LintIssue]:
    """
    Validate ``<formalization>`` blocks against rules, vocabulary, and tests.

    Returns lint issues with ``code`` set to ``FORMAL_*`` constants.
    """
    issues: list[LintIssue] = []
    if ir.parse_error:
        return issues

    known_ids = ir.known_rule_ids
    vocab = {t.lower() for t in ir.vocabulary_terms}
    requirements_text = ir.sections.get("requirements", "").lower()
    rules_text = ir.sections.get("contract_rules", "").lower()
    acceptance_text = ir.sections.get("acceptance_tests", "").lower()
    coverage_text = ir.sections.get("coverage", "").lower()
    test_ref_text = " ".join(
        " ".join(refs) for refs in ir.test_refs.values()
    ).lower()

    has_formal_test_ref = bool(
        _FORMAL_TEST_KEYWORDS.search(acceptance_text)
        or _FORMAL_TEST_KEYWORDS.search(coverage_text)
        or _FORMAL_TEST_KEYWORDS.search(test_ref_text)
    )

    for formal in ir.formalizations:
        issues.extend(
            _check_one_formalization(
                formal,
                known_ids=known_ids,
                vocab=vocab,
                requirements_text=requirements_text,
                rules_text=rules_text,
                acceptance_text=acceptance_text,
                has_formal_test_ref=has_formal_test_ref,
                strict=strict,
            )
        )

    # Rules with smt target mentioned in rules but no formalization block
    for rule in ir.rules:
        rid = rule.raw_id.upper()
        if rid in ("(UNNUMBERED)",):
            continue
        if rid in {f.rule_id.upper() for f in ir.formalizations}:
            continue
        if "smt" in rule.text.lower() or "formal" in rule.text.lower():
            level = "error" if strict else "warn"
            issues.append(LintIssue(
                level=level,
                code="FORMAL_RULE_WITHOUT_FORMALIZATION",
                term=rid,
                section="contract_rules",
                line=rule.text[:120],
                message=(
                    f'Rule {rid} mentions formal/SMT verification but has no '
                    f"<formalization> entry."
                ),
            ))

    return issues


def _check_one_formalization(
    formal: "FormalizationRecord",
    *,
    known_ids: set[str],
    vocab: set[str],
    requirements_text: str,
    rules_text: str,
    acceptance_text: str,
    has_formal_test_ref: bool,
    strict: bool,
) -> list[LintIssue]:
    issues: list[LintIssue] = []
    rid = formal.rule_id.upper()
    level = "error" if strict else "warn"
    target = (formal.target or formal.fields.get("target", "")).lower()
    predicate = (formal.predicate or formal.fields.get("predicate", "")).strip()
    violation = (formal.fields.get("violation", "") or "").strip()

    if rid not in known_ids and known_ids:
        issues.append(LintIssue(
            level=level,
            code="FORMAL_UNKNOWN_RULE_ID",
            term=rid,
            section="formalization",
            line=formal.raw_block[:120] if formal.raw_block else rid,
            message=f'Formalization references unknown rule ID "{rid}".',
        ))

    if "smt" in target:
        if not predicate:
            issues.append(LintIssue(
                level=level,
                code="FORMAL_MISSING_PREDICATE",
                term=rid,
                section="formalization",
                line=formal.raw_block[:120] if formal.raw_block else rid,
                message=f'SMT formalization for {rid} is missing predicate:.',
            ))
        else:
            undefined = _undefined_predicate_vars(
                predicate,
                violation,
                formal.fields,
                vocab,
                requirements_text,
                rules_text,
            )
            for var in undefined:
                issues.append(LintIssue(
                    level=level,
                    code="FORMAL_UNDEFINED_VARIABLE",
                    term=var,
                    section="formalization",
                    line=predicate[:120],
                    message=(
                        f'Variable "{var}" in {rid} predicate is not defined in '
                        f"<formalization> variables, <vocabulary>, or <requirements>."
                    ),
                ))
            if not violation and "=>" not in predicate and "!=" not in predicate:
                issues.append(LintIssue(
                    level=level,
                    code="FORMAL_NO_VIOLATION_CASE",
                    term=rid,
                    section="formalization",
                    line=predicate[:120],
                    message=(
                        f'SMT formalization for {rid} should include violation: '
                        f"or an explicit counterexample form."
                    ),
                ))
            if _uses_unbounded_int(predicate, formal.fields) and not _has_bound(
                predicate, formal.fields
            ):
                issues.append(LintIssue(
                    level=level,
                    code="FORMAL_UNBOUNDED_DOMAIN",
                    term=rid,
                    section="formalization",
                    line=predicate[:120],
                    message=(
                        f'Integer variables in {rid} should declare bounds via '
                        f"assume:, variables:, or explicit <= constraints."
                    ),
                ))
            if not has_formal_test_ref and rid.lower() not in acceptance_text:
                issues.append(LintIssue(
                    level=level,
                    code="FORMAL_NO_TEST_LINK",
                    term=rid,
                    section="formalization",
                    line=formal.raw_block[:120] if formal.raw_block else rid,
                    message=(
                        f'SMT formalization for {rid} has no linked acceptance test '
                        f"or coverage reference (z3/smt/formal/proof/bounded)."
                    ),
                ))

    return issues


def _undefined_predicate_vars(
    predicate: str,
    violation: str,
    fields: dict[str, str],
    vocab: set[str],
    requirements_text: str,
    rules_text: str,
) -> list[str]:
    variables_block = fields.get("variables", "")
    known: set[str] = set()
    for line in variables_block.splitlines():
        m = re.match(r"^\s*([a-z_][a-z0-9_]*)\s*:", line, re.IGNORECASE)
        if m:
            known.add(m.group(1).lower())
    for key in fields:
        if key not in ("variables", "violation", "predicate", "target", "level", "status"):
            known.add(key.lower())

    combined = f"{predicate} {violation} {requirements_text} {rules_text}"
    undefined: list[str] = []
    for var in _PREDICATE_VAR_RE.findall(f"{predicate} {violation}"):
        low = var.lower()
        if low in _PREDICATE_KEYWORDS or low in known or low in vocab:
            continue
        if low in combined and low in requirements_text.split():
            continue
        if re.search(rf"\b{re.escape(low)}\b", requirements_text + rules_text):
            continue
        if low not in undefined:
            undefined.append(low)
    return undefined


def _uses_unbounded_int(predicate: str, fields: dict[str, str]) -> bool:
    text = predicate.lower() + fields.get("variables", "").lower()
    return "int" in text or re.search(r"\b\d+\b", predicate) is not None


def _has_bound(predicate: str, fields: dict[str, str]) -> bool:
    combined = predicate + fields.get("assume", "") + fields.get("variables", "")
    return bool(
        re.search(r"\b(assume|bound|<=|>=|<|>)\b", combined, re.IGNORECASE)
    )


def build_formalization_report(ir: "PromptContractIR") -> list[dict]:
    """Build per-rule formalization readiness rows for ``--report formalization``."""
    rows: list[dict] = []
    formal_by_id = {f.rule_id.upper(): f for f in ir.formalizations}
    acceptance = ir.sections.get("acceptance_tests", "")
    coverage = ir.sections.get("coverage", "")

    for rid in ir.rule_ids:
        formal = formal_by_id.get(rid)
        target = ""
        predicate_yes = False
        variables_yes = False
        violation_yes = False
        if formal:
            target = formal.target or formal.fields.get("target", "")
            predicate_yes = bool((formal.predicate or formal.fields.get("predicate", "")).strip())
            variables_yes = bool(formal.fields.get("variables", "").strip())
            violation_yes = bool(formal.fields.get("violation", "").strip())
        test_link = bool(
            _FORMAL_TEST_KEYWORDS.search(acceptance)
            and rid.lower() in acceptance.lower()
        ) or rid in coverage
        gate_issues = [
            i.as_dict() for i in check_formalization(ir, strict=False)
            if i.term == rid or (formal and i.section == "formalization")
        ]
        rows.append({
            "rule_id": rid,
            "target": target,
            "predicate": predicate_yes,
            "variables": variables_yes,
            "violation": violation_yes,
            "test_link": test_link,
            "issues": gate_issues,
        })
    return rows
