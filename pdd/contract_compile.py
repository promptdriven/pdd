# pylint: disable=too-many-locals
"""
Compile prompt <contract_rules> into a deterministic contract IR.

This is intentionally conservative. It does not try to prove arbitrary prose.
It extracts stable rule IDs, simple When-conditions, and observable obligations
that later verification adapters can consume.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from .contract_ir import Rule, parse_prompt_contracts

_WHEN_RE = re.compile(
    r"\bwhen\s+(.*?)(?:,\s+the\s+|\s+the\s+|\.\s+|$)",
    re.IGNORECASE | re.DOTALL,
)
_HTTP_RE = re.compile(
    r"\b(MUST(?:\s+NOT)?|SHOULD(?:\s+NOT)?|MAY(?:\s+NOT)?|SHALL(?:\s+NOT)?)"
    r"\s+return\s+HTTP\s+(\d{3})\b",
    re.IGNORECASE,
)
_RETURN_RE = re.compile(
    r"\b(MUST(?:\s+NOT)?|SHOULD(?:\s+NOT)?|MAY(?:\s+NOT)?|SHALL(?:\s+NOT)?)"
    r"\s+return\s+(?!HTTP\b)([^;\n]+?)"
    r"(?=(?:\s+and\s+(?:MUST|SHOULD|MAY|SHALL)\b)|[.;](?:\s|$)|$)",
    re.IGNORECASE,
)
_WRITE_RE = re.compile(
    r"\b(MUST(?:\s+NOT)?|SHOULD(?:\s+NOT)?|MAY(?:\s+NOT)?|SHALL(?:\s+NOT)?)"
    r"\s+(write|store|save|append|insert|update|delete|remove)\s+"
    r"([^.;\n]+)",
    re.IGNORECASE,
)
_CALL_RE = re.compile(
    r"\b(MUST(?:\s+NOT)?|SHOULD(?:\s+NOT)?|MAY(?:\s+NOT)?|SHALL(?:\s+NOT)?)"
    r"\s+call\s+([^;\n]+?)"
    r"(?=(?:\s+and\s+(?:MUST|SHOULD|MAY|SHALL)\b)|[.;](?:\s|$)|$)",
    re.IGNORECASE,
)
_EMIT_RE = re.compile(
    r"\b(MUST(?:\s+NOT)?|SHOULD(?:\s+NOT)?|MAY(?:\s+NOT)?|SHALL(?:\s+NOT)?)"
    r"\s+emit\s+([^;\n]+?)"
    r"(?=(?:\s+and\s+(?:MUST|SHOULD|MAY|SHALL)\b)|[.;](?:\s|$)|$)",
    re.IGNORECASE,
)
_RAISE_RE = re.compile(
    r"\b(MUST(?:\s+NOT)?|SHOULD(?:\s+NOT)?|MAY(?:\s+NOT)?|SHALL(?:\s+NOT)?)"
    r"\s+raise\s+([^;\n]+?)"
    r"(?=(?:\s+and\s+(?:MUST|SHOULD|MAY|SHALL)\b)|[.;](?:\s|$)|$)",
    re.IGNORECASE,
)
_ID_TITLE_RE = re.compile(
    r"^(R-?\d+|RULE-?\d+)\s*(?:[-:.)]\s*)?(.*)$",
    re.IGNORECASE,
)


@dataclass
class CompileError:
    """A deterministic reason a contract rule could not compile cleanly."""

    code: str
    rule_id: str
    message: str
    line: str

    def as_dict(self) -> dict[str, str]:
        """Return a JSON-safe representation."""
        return {
            "code": self.code,
            "rule_id": self.rule_id,
            "message": self.message,
            "line": self.line,
        }


@dataclass
class Obligation:
    """One machine-readable obligation extracted from a contract rule."""

    modal: str
    type: str
    value: dict[str, Any]
    text: str

    def as_dict(self) -> dict[str, Any]:
        """Return a JSON-safe representation."""
        return {
            "modal": self.modal,
            "type": self.type,
            "value": self.value,
            "text": self.text,
        }


@dataclass
class CompiledRule:
    """One compiled rule in the contract IR."""

    id: str
    title: str
    modal: str
    condition: str
    obligations: list[Obligation] = field(default_factory=list)
    raw: str = ""

    def as_dict(self) -> dict[str, Any]:
        """Return a JSON-safe representation."""
        return {
            "id": self.id,
            "title": self.title,
            "modal": self.modal,
            "condition": self.condition,
            "obligations": [obligation.as_dict() for obligation in self.obligations],
            "raw": self.raw,
        }


@dataclass
class ContractIR:
    """Compiled contract IR for one prompt file."""

    path: Path
    version: str = "pdd.contract_ir.v1"
    has_contract_rules: bool = False
    rules: list[CompiledRule] = field(default_factory=list)
    compile_errors: list[CompileError] = field(default_factory=list)

    @property
    def rule_count(self) -> int:
        """Number of compiled rules."""
        return len(self.rules)

    @property
    def error_count(self) -> int:
        """Number of compile errors."""
        return len(self.compile_errors)

    def as_dict(self) -> dict[str, Any]:
        """Return a JSON-safe representation."""
        return {
            "version": self.version,
            "path": str(self.path),
            "has_contract_rules": self.has_contract_rules,
            "rule_count": self.rule_count,
            "error_count": self.error_count,
            "rules": [rule.as_dict() for rule in self.rules],
            "compile_errors": [error.as_dict() for error in self.compile_errors],
        }


def compile_prompt(path: Path, *, obligations_only: bool = False) -> ContractIR:  # pylint: disable=unused-argument
    """Compile one prompt file into the v1 contract IR."""
    authoring = parse_prompt_contracts(path)
    result = ContractIR(path=path)
    if authoring.parse_error or not authoring.has_contract_rules:
        return result

    result.has_contract_rules = True
    rules = authoring.rules
    for rule in rules:
        compiled, errors = _compile_rule(rule)
        if compiled is not None:
            result.rules.append(compiled)
        result.compile_errors.extend(errors)
    return result


def compile_directory(directory: Path) -> list[ContractIR]:
    """Compile every *.prompt file under a directory recursively."""
    return [compile_prompt(path) for path in sorted(directory.rglob("*.prompt"))]


def _compile_rule(rule: Rule) -> tuple[CompiledRule | None, list[CompileError]]:
    """Compile one parsed Rule into a CompiledRule plus any compile errors."""
    errors: list[CompileError] = []
    rule_id = rule.raw_id.upper()
    if rule_id == "(UNNUMBERED)" or not _ID_TITLE_RE.match(rule.line):
        errors.append(CompileError(
            code="UNSTABLE_RULE_ID",
            rule_id=rule.raw_id,
            line=rule.line,
            message="Contract rules must use a stable explicit ID such as R1 or R-001.",
        ))
        return None, errors

    title = _extract_title(rule.line)
    condition = _extract_condition(rule.block)
    obligations = _extract_obligations(rule.block)

    if not condition:
        errors.append(CompileError(
            code="MISSING_CONDITION",
            rule_id=rule_id,
            line=rule.line,
            message='Rule must state a parseable condition using "When ...".',
        ))

    if not obligations:
        errors.append(CompileError(
            code="NO_OBSERVABLE_OBLIGATION",
            rule_id=rule_id,
            line=rule.line,
            message=(
                "Rule must contain at least one parseable observable obligation, "
                "such as MUST return HTTP 409 or MUST NOT write a record."
            ),
        ))

    compiled = CompiledRule(
        id=rule_id,
        title=title,
        modal=rule.modal.upper(),
        condition=condition,
        obligations=obligations,
        raw=rule.block,
    )
    return compiled, errors


def _extract_title(line: str) -> str:
    """Extract the optional human title after a rule ID."""
    match = _ID_TITLE_RE.match(line.strip())
    if not match:
        return ""
    return match.group(2).strip()


def _extract_condition(block: str) -> str:
    """Extract a simple When-condition from a rule block."""
    normalized = " ".join(block.split())
    match = _WHEN_RE.search(normalized)
    if not match:
        return ""
    return match.group(1).strip(" ,.")


def _extract_obligations(block: str) -> list[Obligation]:
    """Extract known observable obligation forms from a rule block."""
    obligations: list[Obligation] = []
    normalized = " ".join(block.split())

    for match in _HTTP_RE.finditer(normalized):
        modal = match.group(1).upper()
        status = int(match.group(2))
        obligations.append(Obligation(
            modal=modal,
            type="return",
            value={"http_status": status},
            text=match.group(0),
        ))

    for match in _RETURN_RE.finditer(normalized):
        modal = match.group(1).upper()
        target = _clean_target(match.group(2))
        obligations.append(Obligation(
            modal=modal,
            type="return",
            value={"target": target},
            text=match.group(0),
        ))

    for match in _WRITE_RE.finditer(normalized):
        modal = match.group(1).upper()
        action = match.group(2).lower()
        target = _clean_target(match.group(3))
        obligations.append(Obligation(
            modal=modal,
            type=action,
            value={"target": target},
            text=match.group(0),
        ))

    for pattern, obligation_type in (
        (_CALL_RE, "call"),
        (_EMIT_RE, "emit"),
        (_RAISE_RE, "raise"),
    ):
        for match in pattern.finditer(normalized):
            modal = match.group(1).upper()
            target = _clean_target(match.group(2))
            obligations.append(Obligation(
                modal=modal,
                type=obligation_type,
                value={"target": target},
                text=match.group(0),
            ))

    return obligations


def _clean_target(value: str) -> str:
    """Normalize a captured obligation target."""
    return re.sub(r"\s+", " ", value).strip(" .,:;")
