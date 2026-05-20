# pylint: disable=too-many-lines
"""
Shared contract authoring intermediate representation (IR).

Single parse entry point for ``pdd contracts check``, ``pdd coverage --contracts``,
``pdd contracts compile``, and ``pdd contracts review``.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from datetime import date
from pathlib import Path
from typing import Any, Optional

PROMPT_CONTRACT_IR_VERSION = "pdd.prompt_contract_ir.v1"

# ---------------------------------------------------------------------------
# Regex patterns (shared across contract tooling)
# ---------------------------------------------------------------------------

MODALS: frozenset[str] = frozenset({
    "MUST NOT", "MUST", "MAY NOT", "MAY", "SHOULD NOT", "SHOULD",
    "DOES NOT", "SHALL NOT", "SHALL",
})

_MODAL_PATTERN = re.compile(
    r"\b(" + "|".join(re.escape(m) for m in sorted(MODALS, key=len, reverse=True)) + r")\b",
)

_EXPLICIT_ID_RE = re.compile(r"^(R-?\d+|RULE-?\d+)\b", re.IGNORECASE)
_CANDIDATE_ID_RE = re.compile(r"^([A-Z]{1,5}[-_]\w+)\b", re.IGNORECASE)
_SEQ_ID_RE = re.compile(r"^(\d+)[.):\s]")
_COVERAGE_REF_RE = re.compile(r"\b(R-?\d+|RULE-?\d+)\b", re.IGNORECASE)
_WAIVER_ID_RE = re.compile(r"^(W-?\d+):", re.IGNORECASE)
_WAIVER_REF_RE = re.compile(r"\bWAIVED\s+(W-?\d+)\b", re.IGNORECASE)

_XML_SECTION_RE = re.compile(
    r"<(?P<tag>[a-z_][a-z0-9_]*)>(?P<body>.*?)</(?P=tag)>",
    re.IGNORECASE | re.DOTALL,
)
_MD_HEADING_RE = re.compile(r"^(#{1,3})\s+(.+)$", re.MULTILINE)

# ---------------------------------------------------------------------------
# Parsed entities
# ---------------------------------------------------------------------------


@dataclass
class Rule:
    """One parsed rule from <contract_rules>."""

    raw_id: str
    num: Optional[int]
    modal: str
    line: str
    block: str
    is_must_not: bool = False
    source_line: int = 0
    terms: list[str] = field(default_factory=list)

    @property
    def text(self) -> str:
        """Full rule text (block)."""
        return self.block


@dataclass
class Waiver:
    """One parsed waiver block from <waivers>."""

    raw_id: str
    rule_id: str = ""
    status: str = ""
    reason: str = ""
    approved_by: str = ""
    expires: Optional[date] = None
    follow_up: str = ""
    raw_block: str = ""


@dataclass
class CoverageEntry:
    """Evidence text for one rule from <coverage>."""

    rule_id: str
    evidence: str
    line: str = ""


@dataclass
class ReviewRecord:
    """One human/LLM review decision from <contract_review>."""

    finding_id: str
    rule_id: str = ""
    status: str = ""
    reviewer: str = ""
    reason: str = ""
    review_date: str = ""
    assigned_to: str = ""
    raw_block: str = ""


@dataclass
class FormalizationRecord:
    """One rule formalization stub from <formalization> (parse-only in v1)."""

    rule_id: str
    level: str = ""
    target: str = ""
    predicate: str = ""
    status: str = ""
    raw_block: str = ""
    fields: dict[str, str] = field(default_factory=dict)


@dataclass
class PromptContractIR:
    """Authoring IR for one prompt file."""

    path: Path
    version: str = PROMPT_CONTRACT_IR_VERSION
    sections: dict[str, str] = field(default_factory=dict)
    rules: list[Rule] = field(default_factory=list)
    waivers: list[Waiver] = field(default_factory=list)
    coverage_entries: dict[str, str] = field(default_factory=dict)
    vocabulary_terms: set[str] = field(default_factory=set)
    reviews: list[ReviewRecord] = field(default_factory=list)
    formalizations: list[FormalizationRecord] = field(default_factory=list)
    story_covers: dict[str, list[str]] = field(default_factory=dict)
    test_refs: dict[str, list[str]] = field(default_factory=dict)
    parse_error: Optional[str] = None

    @property
    def has_contract_rules(self) -> bool:
        """True when <contract_rules> is present and non-empty."""
        return bool(self.sections.get("contract_rules", "").strip())

    @property
    def has_contract_sections(self) -> bool:
        """True when any contract-related section exists."""
        keys = {
            "contract_rules", "vocabulary", "capabilities",
            "coverage", "non_responsibilities", "waivers",
            "contract_review", "formalization",
        }
        return any(k in self.sections for k in keys)

    @property
    def rule_ids(self) -> list[str]:
        """Rule IDs in declaration order."""
        return [
            r.raw_id.upper() for r in self.rules
            if r.raw_id not in ("(unnumbered)",)
        ]

    @property
    def known_rule_ids(self) -> set[str]:
        """Set of known rule IDs."""
        return set(self.rule_ids)

    @property
    def known_waiver_ids(self) -> set[str]:
        """Set of known waiver IDs."""
        return {w.raw_id.upper() for w in self.waivers}

    def rule_by_id(self, rule_id: str) -> Optional[Rule]:
        """Return a rule by ID (case-insensitive)."""
        target = rule_id.upper()
        for rule in self.rules:
            if rule.raw_id.upper() == target:
                return rule
        return None

    def as_dict(self) -> dict[str, Any]:
        """JSON-safe authoring IR."""
        return {
            "version": self.version,
            "path": str(self.path),
            "has_contract_rules": self.has_contract_rules,
            "parse_error": self.parse_error,
            "rules": [
                {
                    "id": r.raw_id.upper(),
                    "modal": r.modal,
                    "text": r.block,
                    "line": r.line,
                    "source_line": r.source_line,
                    "is_must_not": r.is_must_not,
                    "terms": r.terms,
                    "coverage": {
                        "stories": self.story_covers.get(r.raw_id.upper(), []),
                        "tests": self.test_refs.get(r.raw_id.upper(), []),
                        "evidence": self.coverage_entries.get(r.raw_id.upper(), ""),
                        "waivers": [
                            w.raw_id for w in self.waivers
                            if w.rule_id.upper() == r.raw_id.upper()
                        ],
                    },
                }
                for r in self.rules
                if r.raw_id not in ("(unnumbered)",)
            ],
            "vocabulary": sorted(self.vocabulary_terms),
            "waivers": [
                {
                    "id": w.raw_id,
                    "rule_id": w.rule_id,
                    "reason": w.reason,
                    "approved_by": w.approved_by,
                    "expires": w.expires.isoformat() if w.expires else None,
                }
                for w in self.waivers
            ],
            "reviews": [
                {
                    "finding_id": rev.finding_id,
                    "rule_id": rev.rule_id,
                    "status": rev.status,
                    "reviewer": rev.reviewer,
                    "reason": rev.reason,
                    "date": rev.review_date,
                    "assigned_to": rev.assigned_to,
                }
                for rev in self.reviews
            ],
            "formalizations": [
                {
                    "rule_id": f.rule_id,
                    "level": f.level,
                    "target": f.target,
                    "status": f.status,
                }
                for f in self.formalizations
            ],
        }


# ---------------------------------------------------------------------------
# Section extraction
# ---------------------------------------------------------------------------


def _extract_xml_sections(text: str) -> dict[str, str]:
    """Return tag-name → inner text for XML-style sections."""
    scan_text = "\n".join(
        line for line in text.splitlines()
        if not line.lstrip().startswith("%")
    )
    sections: dict[str, str] = {}
    for section_match in _XML_SECTION_RE.finditer(scan_text):
        tag = section_match.group("tag").lower()
        sections[tag] = section_match.group("body")
    return sections


def _extract_markdown_sections(text: str) -> dict[str, str]:
    """Return lowered-heading → body for markdown ## / ### headings."""
    headings = list(_MD_HEADING_RE.finditer(text))
    sections: dict[str, str] = {}
    for idx, match in enumerate(headings):
        heading_text = match.group(2).strip().lower()
        start = match.end()
        end = headings[idx + 1].start() if idx + 1 < len(headings) else len(text)
        sections[heading_text] = text[start:end].strip()
    return sections


def extract_sections(text: str) -> dict[str, str]:
    """
    Return section-name → inner text for XML tags and markdown headings.

    Ignores ``%`` comment lines in XML scanning so literal tag names in comments
    cannot pair with real closing tags.
    """
    sections: dict[str, str] = {}
    sections.update(_extract_xml_sections(text))
    sections.update(_extract_markdown_sections(text))
    return sections


# ---------------------------------------------------------------------------
# Rule / waiver / coverage parsers
# ---------------------------------------------------------------------------


def extract_rules(rules_text: str) -> list[Rule]:  # pylint: disable=too-many-locals
    """Parse <contract_rules> text into Rule objects."""
    rules: list[Rule] = []
    lines = rules_text.splitlines()
    line_count = len(lines)
    i = 0

    while i < line_count:
        stripped = lines[i].strip()
        source_line = i + 1
        i += 1

        if not stripped:
            continue

        explicit = _EXPLICIT_ID_RE.match(stripped)
        seq = _SEQ_ID_RE.match(stripped)
        is_bullet = stripped.startswith(("-", "*", "•"))

        if not (explicit or seq or is_bullet):
            continue

        if explicit:
            raw_id = explicit.group(1).upper()
            num_str = re.search(r"\d+", raw_id)
            num = int(num_str.group()) if num_str else None
        elif seq:
            num = int(seq.group(1))
            raw_id = f"S-{num:03d}"
        else:
            raw_id = "(unnumbered)"
            num = None

        header_line = stripped
        block_lines = [stripped]
        blank_run = 0

        while i < line_count:
            next_stripped = lines[i].strip()
            if not next_stripped:
                blank_run += 1
                if blank_run >= 2:
                    i += 1
                    break
                i += 1
                continue
            blank_run = 0
            if (_EXPLICIT_ID_RE.match(next_stripped) or
                    _SEQ_ID_RE.match(next_stripped) or
                    next_stripped.startswith(("-", "*", "•"))):
                break
            block_lines.append(next_stripped)
            i += 1

        block = "\n".join(block_lines)
        modal_match = _MODAL_PATTERN.search(block)
        modal = modal_match.group(1) if modal_match else ""
        is_must_not = bool(
            re.search(r"\bMUST NOT\b|\bSHALL NOT\b|\bMAY NOT\b", block)
        )
        terms = _extract_rule_terms(block)

        rules.append(Rule(
            raw_id=raw_id,
            num=num,
            modal=modal,
            line=header_line,
            block=block,
            is_must_not=is_must_not,
            source_line=source_line,
            terms=terms,
        ))

    return rules


def _extract_rule_terms(block: str) -> list[str]:
    """Extract vocabulary-like terms referenced in a rule block."""
    from .prompt_lint import VAGUE_TERMS  # pylint: disable=import-outside-toplevel

    found: list[str] = []
    lower_block = block.lower()
    for term in sorted(VAGUE_TERMS):
        if re.search(rf"\b{re.escape(term)}\b", lower_block):
            found.append(term)
    return found


def extract_waivers(waivers_text: str) -> list[Waiver]:
    """Parse <waivers> text into Waiver objects."""
    waivers: list[Waiver] = []
    current_id: Optional[str] = None
    current_fields: dict[str, str] = {}
    current_block_lines: list[str] = []

    def _flush() -> None:
        if current_id is None:
            return
        waiver = Waiver(
            raw_id=current_id,
            rule_id=current_fields.get("rule", ""),
            status=current_fields.get("status", ""),
            reason=current_fields.get("reason", ""),
            approved_by=current_fields.get("approved by", ""),
            follow_up=current_fields.get("follow-up", ""),
            raw_block="\n".join(current_block_lines),
        )
        expires_str = current_fields.get("expires", "")
        if expires_str:
            try:
                waiver.expires = date.fromisoformat(expires_str.strip())
            except ValueError:
                pass
        rule_ref = _COVERAGE_REF_RE.search(waiver.rule_id)
        if rule_ref:
            waiver.rule_id = rule_ref.group(1).upper()
        waivers.append(waiver)

    for line in waivers_text.splitlines():
        stripped = line.strip()
        waiver_hdr = _WAIVER_ID_RE.match(stripped)
        if waiver_hdr:
            _flush()
            current_id = waiver_hdr.group(1).upper()
            current_fields = {}
            current_block_lines = [stripped]
            continue
        if current_id is not None:
            current_block_lines.append(stripped)
            kv_match = re.match(r"^([A-Za-z][A-Za-z\s\-]*?):\s*(.+)$", stripped)
            if kv_match:
                current_fields[kv_match.group(1).strip().lower()] = kv_match.group(2).strip()

    _flush()
    return waivers


def parse_coverage_block(coverage_text: str) -> dict[str, str]:
    """Parse <coverage> into rule_id → evidence_text."""
    entries: dict[str, str] = {}
    for line in coverage_text.splitlines():
        stripped = line.strip().lstrip("-* ")
        if not stripped:
            continue
        ref_match = _COVERAGE_REF_RE.match(stripped)
        if ref_match:
            rid = ref_match.group(1).upper()
            rest = stripped[ref_match.end():].lstrip(":").strip()
            entries[rid] = rest
    return entries


def parse_waiver_rule_map(waivers_text: str) -> dict[str, str]:
    """Return mapping rule_id → waiver_id from <waivers>."""
    rule_to_waiver: dict[str, str] = {}
    current_waiver_id: Optional[str] = None

    for line in waivers_text.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        waiver_header = _WAIVER_ID_RE.match(stripped)
        if waiver_header:
            current_waiver_id = waiver_header.group(1).upper()
            continue
        if current_waiver_id and stripped.lower().startswith("rule:"):
            rule_val = stripped[5:].strip().upper()
            ref_match = _COVERAGE_REF_RE.search(rule_val)
            if ref_match:
                rule_to_waiver[ref_match.group(1).upper()] = current_waiver_id

    return rule_to_waiver


def parse_rule_ids(rules_text: str) -> list[str]:
    """Extract rule IDs from <contract_rules> in declaration order."""
    rule_ids: list[str] = []
    seen: set[str] = set()

    for line in rules_text.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        explicit = _EXPLICIT_ID_RE.match(stripped)
        seq = _SEQ_ID_RE.match(stripped)
        if explicit:
            rid = explicit.group(1).upper()
        elif seq:
            rid = f"S-{int(seq.group(1)):03d}"
        else:
            continue
        if rid not in seen:
            seen.add(rid)
            rule_ids.append(rid)

    return rule_ids


def _parse_review_section(review_text: str) -> list[ReviewRecord]:
    """Parse <contract_review> blocks."""
    records: list[ReviewRecord] = []
    current_id: Optional[str] = None
    fields: dict[str, str] = {}
    block_lines: list[str] = []

    def _flush() -> None:
        if current_id is None:
            return
        records.append(ReviewRecord(
            finding_id=current_id,
            rule_id=fields.get("rule", ""),
            status=fields.get("status", ""),
            reviewer=fields.get("reviewer", ""),
            reason=fields.get("reason", ""),
            review_date=fields.get("date", ""),
            assigned_to=fields.get("assigned to", fields.get("assigned_to", "")),
            raw_block="\n".join(block_lines),
        ))

    for line in review_text.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        header = re.match(r"^(LLM-[A-Za-z0-9_-]+):?\s*$", stripped, re.IGNORECASE)
        if header:
            _flush()
            current_id = header.group(1).upper()
            fields = {}
            block_lines = [stripped]
            continue
        if current_id is not None:
            block_lines.append(stripped)
            kv_match = re.match(r"^([A-Za-z][A-Za-z\s_]*?):\s*(.+)$", stripped)
            if kv_match:
                fields[kv_match.group(1).strip().lower()] = kv_match.group(2).strip()

    _flush()
    return records


def _parse_formalization_section(formal_text: str) -> list[FormalizationRecord]:
    """Parse <formalization> blocks (stub — no verification)."""
    records: list[FormalizationRecord] = []
    current_rule: Optional[str] = None
    fields: dict[str, str] = {}
    block_lines: list[str] = []

    def _flush() -> None:
        if current_rule is None:
            return
        records.append(FormalizationRecord(
            rule_id=current_rule,
            level=fields.get("level", ""),
            target=fields.get("target", ""),
            predicate=fields.get("predicate", ""),
            status=fields.get("status", ""),
            raw_block="\n".join(block_lines),
            fields=dict(fields),
        ))

    for line in formal_text.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        rule_hdr = re.match(r"^(R-?\d+|RULE-?\d+):?\s*$", stripped, re.IGNORECASE)
        if rule_hdr:
            _flush()
            current_rule = rule_hdr.group(1).upper()
            fields = {}
            block_lines = [stripped]
            continue
        if current_rule is not None:
            block_lines.append(stripped)
            kv_match = re.match(r"^([A-Za-z][A-Za-z_]*?):\s*(.+)$", stripped)
            if kv_match:
                fields[kv_match.group(1).strip().lower()] = kv_match.group(2).strip()

    _flush()
    return records


def _build_vocabulary_terms(sections: dict[str, str]) -> set[str]:
    """Collect defined vocabulary terms from prompt sections."""
    from .prompt_lint import _extract_vocabulary_terms  # pylint: disable=import-outside-toplevel

    vocab_terms: set[str] = set()
    for key in ("vocabulary", "glossary", "definitions", "covers"):
        if key in sections:
            vocab_terms |= _extract_vocabulary_terms(sections[key])
    return vocab_terms


# ---------------------------------------------------------------------------
# Public parse API
# ---------------------------------------------------------------------------


def parse_prompt_contracts(
    path: Path,
    *,
    stories_dir: Optional[Path] = None,
    tests_dir: Optional[Path] = None,
) -> PromptContractIR:
    """
    Parse one prompt file into the shared authoring IR.

    When ``stories_dir`` / ``tests_dir`` are provided, optional evidence maps
    are populated (same scanners as coverage).
    """
    ir = PromptContractIR(path=path)

    try:
        text = path.read_text(encoding="utf-8")
    except FileNotFoundError:
        ir.parse_error = f'File not found: "{path}"'
        return ir
    except OSError as exc:
        ir.parse_error = str(exc)
        return ir

    ir.sections = extract_sections(text)
    ir.vocabulary_terms = _build_vocabulary_terms(ir.sections)

    rules_text = ir.sections.get("contract_rules", "")
    if rules_text.strip():
        ir.rules = extract_rules(rules_text)

    waivers_text = ir.sections.get("waivers", "")
    if waivers_text.strip():
        ir.waivers = extract_waivers(waivers_text)

    coverage_text = ir.sections.get("coverage", "")
    if coverage_text.strip():
        ir.coverage_entries = parse_coverage_block(coverage_text)

    review_text = ir.sections.get("contract_review", "")
    if review_text.strip():
        ir.reviews = _parse_review_section(review_text)

    formal_text = ir.sections.get("formalization", "")
    if formal_text.strip():
        ir.formalizations = _parse_formalization_section(formal_text)

    if stories_dir is not None:
        from .coverage_contracts import scan_story_evidence  # pylint: disable=import-outside-toplevel
        ir.story_covers = scan_story_evidence(stories_dir, path)

    if tests_dir is not None:
        from .coverage_contracts import scan_test_evidence  # pylint: disable=import-outside-toplevel
        ir.test_refs = scan_test_evidence(tests_dir)

    return ir


def parse_directory(
    directory: Path,
    *,
    stories_dir: Optional[Path] = None,
    tests_dir: Optional[Path] = None,
) -> list[PromptContractIR]:
    """Parse every ``*.prompt`` file under a directory."""
    return [
        parse_prompt_contracts(p, stories_dir=stories_dir, tests_dir=tests_dir)
        for p in sorted(directory.rglob("*.prompt"))
    ]
