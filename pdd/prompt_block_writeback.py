"""
Write-back helpers for contract blocks produced by prompt lint / formalize.
"""
from __future__ import annotations

import re
from pathlib import Path

from .prompt_lint import _extract_sections
from .prompt_lint_schemas import FormalizationCandidate, FormalizeBundle

_CONTRACT_RULES_OPEN = "<contract_rules>"
_CONTRACT_RULES_CLOSE = "</contract_rules>"
_ACCEPTANCE_OPEN = "<acceptance_tests>"
_ACCEPTANCE_CLOSE = "</acceptance_tests>"
_FORMALIZATION_OPEN = "<formalization>"
_FORMALIZATION_CLOSE = "</formalization>"
_COVERAGE_OPEN = "<coverage>"
_COVERAGE_CLOSE = "</coverage>"

_RULE_ID_RE = re.compile(r"^(R-?\d+|RULE-?\d+)\b", re.IGNORECASE)


def append_contract_rules(path: Path, rewrites: list[str]) -> int:
    """Merge rule rewrites by rule ID into ``<contract_rules>``."""
    cleaned = [r.strip() for r in rewrites if r.strip()]
    if not cleaned:
        return 0
    text = path.read_text(encoding="utf-8")
    sections = _extract_sections(text)
    existing_body = sections.get("contract_rules", "")
    by_id: dict[str, str] = {}
    for block in _split_rule_blocks(existing_body):
        rid = _rule_id_from_block(block)
        if rid:
            by_id[rid] = block
    written = 0
    for rewrite in cleaned:
        rid = _rule_id_from_block(rewrite)
        if not rid:
            continue
        if by_id.get(rid) == rewrite:
            continue
        by_id[rid] = rewrite
        written += 1
    if written == 0:
        return 0
    new_body = "\n".join(by_id[r] for r in sorted(by_id.keys(), key=_rule_sort_key))
    return _replace_or_append_section(
        path, text, "contract_rules", _CONTRACT_RULES_OPEN, _CONTRACT_RULES_CLOSE, new_body
    ) or written


def append_acceptance_tests(path: Path, criteria: list[str]) -> int:
    """Append acceptance test bullets under ``<acceptance_tests>``."""
    cleaned = []
    for c in criteria:
        line = c.strip()
        if not line:
            continue
        if not line.startswith("-"):
            line = f"- {line}"
        cleaned.append(line)
    if not cleaned:
        return 0
    text = path.read_text(encoding="utf-8")
    sections = _extract_sections(text)
    existing = sections.get("acceptance_tests", "")
    existing_lines = {ln.strip() for ln in existing.splitlines() if ln.strip()}
    new_lines = [ln for ln in cleaned if ln.strip() not in existing_lines]
    if not new_lines:
        return 0
    new_body = (existing.rstrip() + "\n" + "\n".join(new_lines)).strip()
    count = len(new_lines)
    _replace_or_append_section(
        path, text, "acceptance_tests", _ACCEPTANCE_OPEN, _ACCEPTANCE_CLOSE, new_body
    )
    return count


def append_formalization(path: Path, candidates: list[FormalizationCandidate]) -> int:
    """Append or replace formalization blocks by rule_id."""
    if not candidates:
        return 0
    text = path.read_text(encoding="utf-8")
    sections = _extract_sections(text)
    existing = sections.get("formalization", "")
    by_id: dict[str, str] = {}
    for block in _split_formal_blocks(existing):
        rid = _rule_id_from_block(block)
        if rid:
            by_id[rid] = block
    written = 0
    for cand in candidates:
        block = _render_formalization_block(cand)
        rid = cand.rule_id.upper()
        if by_id.get(rid) == block:
            continue
        by_id[rid] = block
        written += 1
    if written == 0:
        return 0
    new_body = "\n\n".join(by_id[r] for r in sorted(by_id.keys(), key=_rule_sort_key))
    _replace_or_append_section(
        path, text, "formalization", _FORMALIZATION_OPEN, _FORMALIZATION_CLOSE, new_body
    )
    return written


def apply_formalize_bundle(path: Path, bundle: FormalizeBundle) -> dict[str, int]:
    """Apply a validated formalize bundle; return per-section write counts."""
    counts = {
        "contract_rules": append_contract_rules(path, bundle.contract_rules),
        "acceptance_tests": append_acceptance_tests(path, bundle.acceptance_tests),
        "formalization": append_formalization(path, bundle.formalization),
    }
    return counts


def _render_formalization_block(cand: FormalizationCandidate) -> str:
    lines = [f"{cand.rule_id}:"]
    if cand.target:
        lines.append(f"  target: {cand.target}")
    if cand.variables:
        lines.append("  variables:")
        for name, typ in cand.variables.items():
            lines.append(f"    {name}: {typ}")
    if cand.assume:
        lines.append(f"  assume: {cand.assume}")
    if cand.predicate:
        lines.append(f"  predicate: {cand.predicate}")
    if cand.violation:
        lines.append(f"  violation: {cand.violation}")
    return "\n".join(lines)


def _split_rule_blocks(body: str) -> list[str]:
    if not body.strip():
        return []
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
    return blocks


def _split_formal_blocks(body: str) -> list[str]:
    return _split_rule_blocks(body)


def _rule_id_from_block(block: str) -> str:
    first = block.strip().splitlines()[0] if block.strip() else ""
    m = _RULE_ID_RE.match(first.rstrip(":"))
    return m.group(1).upper() if m else ""


def _rule_sort_key(rid: str) -> tuple[int, str]:
    m = re.search(r"(\d+)", rid)
    return (int(m.group(1)) if m else 0, rid)


def _replace_or_append_section(
    path: Path,
    text: str,
    _section_key: str,
    open_tag: str,
    close_tag: str,
    new_body: str,
) -> int:
    if open_tag in text and close_tag in text:
        pattern = re.compile(
            re.escape(open_tag) + r".*?" + re.escape(close_tag),
            re.DOTALL | re.IGNORECASE,
        )
        replacement = f"{open_tag}\n{new_body}\n{close_tag}"
        text = pattern.sub(replacement, text, count=1)
    else:
        text = text.rstrip() + f"\n\n{open_tag}\n{new_body}\n{close_tag}\n"
    path.write_text(text, encoding="utf-8")
    return 1
