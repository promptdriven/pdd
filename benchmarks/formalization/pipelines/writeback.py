"""Deterministic prompt section write-back for the formalization benchmark.

Benchmark-local: does not require ``pdd checkup lint --apply`` in the product CLI.
"""
from __future__ import annotations

import re
from pathlib import Path

_VOCABULARY_OPEN = "<vocabulary>"
_VOCABULARY_CLOSE = "</vocabulary>"
_CONTRACT_RULES_OPEN = "<contract_rules>"
_CONTRACT_RULES_CLOSE = "</contract_rules>"
_ACCEPTANCE_OPEN = "<acceptance_tests>"
_ACCEPTANCE_CLOSE = "</acceptance_tests>"
_FORMALIZATION_OPEN = "<formalization>"
_FORMALIZATION_CLOSE = "</formalization>"

_XML_SECTION_RE = re.compile(
    r"<(?P<tag>[a-zA-Z_][\w-]*)>(?P<body>.*?)</(?P=tag)>",
    re.DOTALL,
)
_RULE_ID_RE = re.compile(r"^(R-?\d+|RULE-?\d+)\b", re.IGNORECASE)


def extract_sections(text: str) -> dict[str, str]:
    """Return lowercased tag name → inner body for XML-style sections."""
    return {
        match.group("tag").lower(): match.group("body").strip()
        for match in _XML_SECTION_RE.finditer(text)
    }


def _replace_or_append_section(
    path: Path,
    text: str,
    section_key: str,
    open_tag: str,
    close_tag: str,
    new_body: str,
) -> int:
    """Replace or append a section; return 1 if the file was written."""
    new_body = new_body.strip()
    if not new_body:
        return 0
    if open_tag in text and close_tag in text:
        pattern = re.compile(
            re.escape(open_tag) + r".*?" + re.escape(close_tag),
            re.DOTALL,
        )
        replacement = f"{open_tag}\n{new_body}\n{close_tag}"
        updated = pattern.sub(replacement, text, count=1)
    else:
        updated = text.rstrip() + f"\n\n{open_tag}\n{new_body}\n{close_tag}\n"
    if updated != text:
        path.write_text(updated, encoding="utf-8")
        return 1
    return 0


def append_vocabulary_definitions(path: Path, suggestions: list[str]) -> int:
    """Append concrete vocabulary lines; skip placeholders and duplicates."""
    cleaned = [
        s.strip().lstrip("- ").strip()
        for s in suggestions
        if s.strip() and "<add a precise" not in s
    ]
    if not cleaned:
        return 0

    text = path.read_text(encoding="utf-8")
    sections = extract_sections(text)
    existing = {
        line.strip().lstrip("- ").strip()
        for line in sections.get("vocabulary", "").splitlines()
        if line.strip()
    }
    new_lines = [s for s in cleaned if s not in existing]
    if not new_lines:
        return 0

    new_entries = "\n".join(f"- {line}" for line in new_lines)
    if _VOCABULARY_OPEN in text and _VOCABULARY_CLOSE in text:
        updated = text.replace(
            _VOCABULARY_CLOSE,
            f"{new_entries}\n{_VOCABULARY_CLOSE}",
        )
    else:
        updated = text.rstrip() + (
            f"\n\n{_VOCABULARY_OPEN}\n{new_entries}\n{_VOCABULARY_CLOSE}\n"
        )
    path.write_text(updated, encoding="utf-8")
    return len(new_lines)


def _rule_id_from_block(block: str) -> str:
    first = block.strip().splitlines()[0] if block.strip() else ""
    match = _RULE_ID_RE.match(first.strip())
    return match.group(1).upper() if match else ""


def _split_rule_blocks(body: str) -> list[str]:
    blocks: list[str] = []
    current: list[str] = []
    for line in body.splitlines():
        if _RULE_ID_RE.match(line.strip()) and current:
            blocks.append("\n".join(current).strip())
            current = [line]
        else:
            current.append(line)
    if current:
        blocks.append("\n".join(current).strip())
    return [b for b in blocks if b]


def append_contract_rules(path: Path, rewrites: list[str]) -> int:
    """Merge rule rewrites by rule ID into ``<contract_rules>``."""
    cleaned = [r.strip() for r in rewrites if r.strip()]
    if not cleaned:
        return 0

    text = path.read_text(encoding="utf-8")
    sections = extract_sections(text)
    by_id: dict[str, str] = {}
    for block in _split_rule_blocks(sections.get("contract_rules", "")):
        rule_id = _rule_id_from_block(block)
        if rule_id:
            by_id[rule_id] = block

    written = 0
    for rewrite in cleaned:
        rule_id = _rule_id_from_block(rewrite)
        if not rule_id or by_id.get(rule_id) == rewrite:
            continue
        by_id[rule_id] = rewrite
        written += 1

    if written == 0:
        return 0

    new_body = "\n".join(by_id[rid] for rid in sorted(by_id))
    _replace_or_append_section(
        path, text, "contract_rules",
        _CONTRACT_RULES_OPEN, _CONTRACT_RULES_CLOSE, new_body,
    )
    return written


def append_acceptance_tests(path: Path, criteria: list[str]) -> int:
    """Append acceptance test bullets under ``<acceptance_tests>``."""
    cleaned: list[str] = []
    for item in criteria:
        line = item.strip()
        if not line:
            continue
        if not line.startswith("-"):
            line = f"- {line}"
        cleaned.append(line)
    if not cleaned:
        return 0

    text = path.read_text(encoding="utf-8")
    sections = extract_sections(text)
    existing = {ln.strip() for ln in sections.get("acceptance_tests", "").splitlines() if ln.strip()}
    new_lines = [ln for ln in cleaned if ln.strip() not in existing]
    if not new_lines:
        return 0

    existing_body = sections.get("acceptance_tests", "")
    new_body = (existing_body.rstrip() + "\n" + "\n".join(new_lines)).strip()
    _replace_or_append_section(
        path, text, "acceptance_tests",
        _ACCEPTANCE_OPEN, _ACCEPTANCE_CLOSE, new_body,
    )
    return len(new_lines)


def append_formalization_block(path: Path, entries: list[str]) -> int:
    """Append formalization candidate blocks."""
    cleaned = [e.strip() for e in entries if e.strip()]
    if not cleaned:
        return 0

    text = path.read_text(encoding="utf-8")
    sections = extract_sections(text)
    existing_body = sections.get("formalization", "")
    existing_set = {block.strip() for block in existing_body.split("\n\n") if block.strip()}
    new_blocks = [b for b in cleaned if b.strip() not in existing_set]
    if not new_blocks:
        return 0

    new_body = (existing_body.rstrip() + "\n\n" + "\n\n".join(new_blocks)).strip()
    _replace_or_append_section(
        path, text, "formalization",
        _FORMALIZATION_OPEN, _FORMALIZATION_CLOSE, new_body,
    )
    return len(new_blocks)


def bootstrap_contract_rules_from_requirements(path: Path) -> int:
    """Create basic R* rules from ``<requirements>`` lines when no rules exist yet."""
    text = path.read_text(encoding="utf-8")
    sections = extract_sections(text)
    if sections.get("contract_rules", "").strip():
        return 0
    requirements = sections.get("requirements", "").strip()
    if not requirements:
        return 0

    rules: list[str] = []
    rule_num = 0
    for line in requirements.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("%"):
            continue
        rule_num += 1
        rules.append(
            f"R{rule_num} - Requirement {rule_num}\n"
            f"When {stripped.rstrip('.')}\n"
            f"The module MUST satisfy this requirement with an observable outcome."
        )
    if not rules:
        return 0
    return append_contract_rules(path, rules)


def merge_formalize_bundle(path: Path, bundle: dict) -> dict[str, int]:
    """Apply a formalize LLM JSON bundle to a prompt file."""
    counts = {
        "vocabulary": 0,
        "contract_rules": 0,
        "acceptance_tests": 0,
        "formalization": 0,
    }
    vocab = bundle.get("vocabulary") or []
    if vocab:
        counts["vocabulary"] = append_vocabulary_definitions(path, list(vocab))
    rules = bundle.get("contract_rules") or []
    if rules:
        counts["contract_rules"] = append_contract_rules(path, list(rules))
    acceptance = bundle.get("acceptance_tests") or []
    if acceptance:
        counts["acceptance_tests"] = append_acceptance_tests(path, list(acceptance))
    formal = bundle.get("formalization") or []
    if formal:
        blocks = [
            entry if isinstance(entry, str) else _format_formalization_entry(entry)
            for entry in formal
        ]
        counts["formalization"] = append_formalization_block(path, blocks)
    return counts


def _format_formalization_entry(entry: dict) -> str:
    """Render one formalization dict as a FORMAL_CANDIDATE block."""
    rule_id = entry.get("rule_id", "R?")
    lines = [f"FORMAL_CANDIDATE {rule_id}"]
    for key in ("target", "variables", "assume", "predicate", "violation", "linked_test"):
        value = entry.get(key)
        if value is not None and value != "":
            lines.append(f"{key}: {value}")
    return "\n".join(lines)
