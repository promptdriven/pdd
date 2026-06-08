"""Generation-readiness pass: extracts requirements from PRD text and gates generation.

Analyzes PRD/issue text to:
- Extract FeatureRequirements from prose using modal verbs and P0/P1 annotations.
- Detect vague phrases using VAGUE_TERMS from contract_ir.
- Classify examples as illustrative or exhaustive.
- Emit ReadingsFindings (blockers/warnings) for underspecified requirements.

All processing is deterministic (no LLM calls).
"""
from __future__ import annotations

import logging
import re
import uuid
from typing import Optional

from pdd.contract_ir import VAGUE_TERMS
from pdd.generation_source_contract import (
    AuditEntryStatus,
    ExampleClassification,
    ExampleKind,
    FeatureRequirement,
    FindingSeverity,
    GenerationSourceContract,
    ReadinessFinding,
    RequirementPriority,
)

logger = logging.getLogger(__name__)

# Modal verb pattern for requirement extraction
_MODAL_RE = re.compile(
    r"(?P<text>[^\n]*?\b(?:MUST|SHALL|SHOULD|REQUIRED|MUST NOT|SHALL NOT)\b[^\n]*)",
    re.IGNORECASE,
)

# P0/P1 annotation pattern
_PRIORITY_RE = re.compile(r"^(P0|P1)[:.\s]", re.IGNORECASE)

# Illustrative example phrases
_ILLUSTRATIVE_RE = re.compile(
    r"\b(?:for example|e\.g\.|for instance|such as|like|including|as in)\b",
    re.IGNORECASE,
)

# Exhaustive example phrases
_EXHAUSTIVE_RE = re.compile(
    r"\b(?:only supported|exactly the following|the following only|exclusively|"
    r"these are the only|the complete list is|only the following)\b",
    re.IGNORECASE,
)


def extract_requirements(prd_text: str) -> list[FeatureRequirement]:
    """Extract FeatureRequirements from PRD text using modal verbs and P0/P1 annotations.

    Returns an empty list for empty input. No LLM calls — pure regex extraction.
    """
    if not prd_text or not prd_text.strip():
        return []

    reqs: list[FeatureRequirement] = []
    seen_descriptions: set[str] = set()

    for idx, line in enumerate(prd_text.splitlines(), start=1):
        line = line.strip()
        if not line:
            continue

        # Determine priority from P0/P1 annotation
        priority = RequirementPriority.p1
        m = _PRIORITY_RE.match(line)
        if m:
            priority = RequirementPriority.p0 if m.group(1).upper() == "P0" else RequirementPriority.p1
            line = line[m.end():].strip()

        # Match modal verb requirements
        modal_match = _MODAL_RE.search(line)
        if modal_match:
            description = line.strip()
            if description and description not in seen_descriptions:
                seen_descriptions.add(description)
                req_id = f"R-{len(reqs) + 1}"

                # Infer kind from description content
                kind = _infer_kind(description)

                # Check vagueness
                is_vague = _has_vague_terms(description)

                reqs.append(
                    FeatureRequirement(
                        req_id=req_id,
                        priority=priority,
                        kind=kind,
                        description=description,
                        is_vague=is_vague,
                    )
                )

    return reqs


def _infer_kind(description: str) -> str:
    """Infer the requirement kind from its description text."""
    low = description.lower()
    if any(kw in low for kw in ("route", "endpoint", "/api/", "post ", "get ", "put ", "delete ")):
        return "api"
    if any(kw in low for kw in ("config", "env", "setting", "yaml", "secret", "key")):
        return "config"
    if any(kw in low for kw in ("test", "spec", "assert")):
        return "test"
    if any(kw in low for kw in ("schema", "model", "pydantic", "type")):
        return "schema"
    if any(kw in low for kw in ("script", "command", "cli", "executable")):
        return "script"
    if any(kw in low for kw in ("export", "import", "function", "method", "class")):
        return "module"
    return "module"


def _has_vague_terms(text: str) -> bool:
    """Return True if the text contains any VAGUE_TERMS."""
    low = text.lower()
    return any(
        re.search(rf"\b{re.escape(term)}\b", low)
        for term in VAGUE_TERMS
    )


def detect_vague_phrases(text: str) -> list[ReadinessFinding]:
    """Detect vague phrases in text using VAGUE_TERMS from contract_ir.

    Returns a list of ReadingsFindings for each unique vague term found.
    Returns an empty list if no vague terms are found.
    """
    if not text:
        return []

    low = text.lower()
    findings: list[ReadinessFinding] = []
    seen_terms: set[str] = set()

    for term in sorted(VAGUE_TERMS):
        if term in seen_terms:
            continue
        if re.search(rf"\b{re.escape(term)}\b", low):
            seen_terms.add(term)
            findings.append(
                ReadinessFinding(
                    finding_id=f"VG-{len(findings) + 1}",
                    kind="vague_requirement",
                    severity=FindingSeverity.blocker,
                    description=(
                        f"Vague phrase detected: '{term}'. "
                        "Requirements containing vague terms cannot be mechanically verified."
                    ),
                    action=(
                        f"Replace '{term}' with a specific, measurable criterion. "
                        "For example, specify exact HTTP status codes, file paths, "
                        "test names, or measurable thresholds."
                    ),
                    resolved=False,
                )
            )

    return findings


def classify_examples(
    requirements: list[FeatureRequirement],
    prd_text: str,
) -> list[ExampleClassification]:
    """Classify examples in PRD text as illustrative or exhaustive.

    Returns an empty list if no requirements are provided.
    """
    if not requirements or not prd_text:
        return []

    classifications: list[ExampleClassification] = []

    has_exhaustive = bool(_EXHAUSTIVE_RE.search(prd_text))
    has_illustrative = bool(_ILLUSTRATIVE_RE.search(prd_text))

    for req in requirements:
        if has_exhaustive:
            kind = ExampleKind.exhaustive
            needs_clarification = False
        elif has_illustrative:
            kind = ExampleKind.illustrative
            needs_clarification = False
        else:
            kind = ExampleKind.unknown
            needs_clarification = True

        classifications.append(
            ExampleClassification(
                feature_req_id=req.req_id,
                kind=kind,
                needs_clarification=needs_clarification,
            )
        )

    return classifications


def analyze_readiness(
    prd_text: str,
    run_id: Optional[str] = None,
) -> GenerationSourceContract:
    """Analyze a PRD/issue text for generation readiness.

    Returns a GenerationSourceContract populated with requirements and
    readiness findings. Raises ValueError if prd_text is empty.

    Blocker findings are emitted when:
    - Requirements contain vague terms from VAGUE_TERMS.
    - P0 requirements lack explicit acceptance criteria.
    """
    if not prd_text or not prd_text.strip():
        raise ValueError("PRD text is empty — cannot analyze generation readiness")

    effective_run_id = run_id or str(uuid.uuid4())
    contract = GenerationSourceContract(run_id=effective_run_id, prd_text=prd_text)

    # 1. Extract requirements
    requirements = extract_requirements(prd_text)
    contract.requirements = requirements

    # 2. Detect vague phrases across the whole PRD text
    vague_findings = detect_vague_phrases(prd_text)
    contract.readiness_findings.extend(vague_findings)

    # 3. Check P0 requirements for missing acceptance criteria
    for req in requirements:
        if req.priority == RequirementPriority.p0 and not req.acceptance_criteria:
            # Only flag as blocker if also vague (otherwise it's a warning)
            severity = FindingSeverity.blocker if req.is_vague else FindingSeverity.warning
            if severity == FindingSeverity.blocker:
                contract.readiness_findings.append(
                    ReadinessFinding(
                        finding_id=f"P0-{req.req_id}",
                        kind="missing_p0_acceptance_criteria",
                        severity=FindingSeverity.blocker,
                        feature_id=req.req_id,
                        description=(
                            f"P0 requirement '{req.req_id}' lacks explicit acceptance criteria "
                            "with file path, endpoint, and test reference."
                        ),
                        action=(
                            "Add explicit acceptance criteria: file path, HTTP status code or "
                            "function signature, and a test reference (e.g. "
                            "`tests/test_payments.py::TestClass::test_method`)."
                        ),
                        resolved=False,
                    )
                )

    # 4. Classify examples
    classifications = classify_examples(requirements, prd_text)
    contract.example_classifications = classifications

    logger.debug(
        "analyze_readiness: run_id=%s, reqs=%d, findings=%d",
        effective_run_id,
        len(requirements),
        len(contract.readiness_findings),
    )

    return contract
