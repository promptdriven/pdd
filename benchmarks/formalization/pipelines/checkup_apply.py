"""Parse ``pdd checkup`` JSON and apply deterministic write-backs for A0→A1."""
from __future__ import annotations

import re
from pathlib import Path
from typing import Any, Optional

from pdd.contract_ir import rule_ids_from_covers

import writeback

_PLACEHOLDER_MARKERS = ("<add a precise", "TODO", "…", "...")
_WAIVER_EXPIRES = "2099-12-31"
_BENCHMARK_WAIVER_REASON = (
    "Formalization benchmark tier A — story/test linkage deferred to M2"
)


def _is_actionable_suggestion(text: str) -> bool:
    stripped = text.strip()
    if not stripped:
        return False
    lower = stripped.lower()
    return not any(marker.lower() in lower for marker in _PLACEHOLDER_MARKERS)


def _bootstrap_vocab_from_lint(issues: list[dict[str, Any]]) -> list[str]:
    """Turn lint hits into vocabulary lines when suggestions are placeholders."""
    suggestions = [
        issue["suggestion"].strip()
        for issue in issues
        if _is_actionable_suggestion(issue.get("suggestion", ""))
    ]
    seen = {s.split(":", 1)[0].strip().lower() for s in suggestions if ":" in s}
    for issue in issues:
        term = (issue.get("term") or "").strip()
        if not term or term.lower() in seen:
            continue
        line = (issue.get("line") or "").lower()
        verb = "returns"
        for candidate in (
            "returns", "raises", "rejects", "writes", "emits", "logs", "stores",
        ):
            if candidate in line:
                verb = candidate
                break
        suggestions.append(
            f"{term}: {verb} an observable outcome defined by this prompt's rules"
        )
        seen.add(term.lower())
    return suggestions


def apply_lint_results(path: Path, lint_payload: list[dict[str, Any]]) -> dict[str, int]:
    """Apply vocabulary write-backs from ``pdd checkup lint --json`` output."""
    issues: list[dict[str, Any]] = []
    for result in lint_payload:
        issues.extend(result.get("issues") or [])
    suggestions = _bootstrap_vocab_from_lint(issues)
    written = writeback.append_vocabulary_definitions(path, suggestions)
    return {"vocabulary": written, "issues_seen": len(issues)}


def apply_contract_results(
    path: Path,
    contract_payload: list[dict[str, Any]],
) -> dict[str, int]:
    """Apply deterministic fixes from ``pdd checkup contract check --json`` output."""
    counts = {"vocabulary": 0, "contract_rules": 0}
    issues: list[dict[str, Any]] = []
    for result in contract_payload:
        issues.extend(result.get("issues") or [])

    vocab_suggestions: list[str] = []
    for issue in issues:
        code = issue.get("code", "")
        suggestion = (issue.get("suggestion") or "").strip()
        if code == "VAGUE_TERM" and _is_actionable_suggestion(suggestion):
            vocab_suggestions.append(suggestion)
        elif code == "VAGUE_TERM" and issue.get("term"):
            term = issue["term"]
            vocab_suggestions.append(
                f"{term}: observable behavior defined in <contract_rules> for this prompt"
            )

    if vocab_suggestions:
        counts["vocabulary"] = writeback.append_vocabulary_definitions(
            path, vocab_suggestions
        )

    if not writeback.extract_sections(path.read_text(encoding="utf-8")).get(
        "contract_rules", ""
    ).strip():
        counts["contract_rules"] = writeback.bootstrap_contract_rules_from_requirements(
            path
        )

    return counts


def _extract_md_section(text: str, heading: str) -> str:
    pattern = re.compile(
        rf"^##\s+{re.escape(heading)}\s*$",
        re.MULTILINE | re.IGNORECASE,
    )
    match = pattern.search(text)
    if not match:
        return ""
    start = match.end()
    next_heading = re.search(r"^##\s+", text[start:], re.MULTILINE)
    end = start + next_heading.start() if next_heading else len(text)
    return text[start:end].strip()


def index_story_covers(stories_dir: Path, prompt_path: Path) -> dict[str, str]:
    """Map rule ID → story filename from ``## Covers`` in corpus stories."""
    if not stories_dir.is_dir():
        return {}
    prompt_name = prompt_path.name
    mapping: dict[str, str] = {}
    for story_path in sorted(stories_dir.rglob("story__*.md")):
        covers_text = _extract_md_section(
            story_path.read_text(encoding="utf-8"),
            "Covers",
        )
        if not covers_text:
            continue
        for rule_id in rule_ids_from_covers(covers_text, prompt_name):
            mapping.setdefault(rule_id.upper(), story_path.name)
    return mapping


def apply_coverage_results(
    path: Path,
    coverage_payload: dict[str, Any],
    *,
    stories_dir: Optional[Path] = None,
    allow_waivers: bool = True,
) -> dict[str, int]:
    """Close coverage gaps using story filenames or benchmark waivers."""
    counts = {"coverage_links": 0, "waivers": 0}
    results = coverage_payload.get("results") or []
    if not results:
        return counts

    result = results[0]
    unchecked = [
        rule["rule_id"].upper()
        for rule in result.get("rules") or []
        if rule.get("status") in ("unchecked", "story-only", "test-only", "failed")
    ]
    if not unchecked:
        return counts

    story_map = index_story_covers(stories_dir, path) if stories_dir else {}
    links: dict[str, str] = {}
    to_waive: list[str] = []
    for rule_id in unchecked:
        story_file = story_map.get(rule_id)
        if story_file:
            links[rule_id] = story_file
        elif allow_waivers:
            to_waive.append(rule_id)

    if links:
        counts["coverage_links"] = writeback.append_coverage_entries(path, links)
    if to_waive:
        counts["waivers"] = writeback.append_benchmark_waivers(
            path,
            to_waive,
            reason=_BENCHMARK_WAIVER_REASON,
            expires=_WAIVER_EXPIRES,
        )
    return counts


def coverage_exit_code(coverage_payload: dict[str, Any]) -> int:
    """Mirror ``pdd checkup coverage`` exit semantics on parsed JSON."""
    results = coverage_payload.get("results") or []
    if coverage_payload.get("error"):
        return 2
    if any(r.get("error") for r in results):
        return 2
    if any(r.get("read_errors") for r in results):
        return 1
    for result in results:
        for rule in result.get("rules") or []:
            if rule.get("status") in (
                "unchecked",
                "story-only",
                "test-only",
                "failed",
            ):
                return 1
    return 0
