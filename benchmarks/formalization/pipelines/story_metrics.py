"""Story template (#820) metrics: Oracle vs Non-Oracle blocks for benchmark arms."""
from __future__ import annotations

import re
from pathlib import Path
from typing import Any, Optional
from unittest.mock import patch

_ORACLE_RE = re.compile(r"^##\s+Oracle\s*$", re.MULTILINE | re.IGNORECASE)
_NON_ORACLE_RE = re.compile(r"^##\s+Non-Oracle\s*$", re.MULTILINE | re.IGNORECASE)
_COVERS_RE = re.compile(r"^##\s+Covers\s*$", re.MULTILINE | re.IGNORECASE)
_BULLET_RE = re.compile(r"^\s*-\s+", re.MULTILINE)


def _section_bullet_count(text: str, header_pattern: re.Pattern[str]) -> int:
    match = header_pattern.search(text)
    if not match:
        return 0
    start = match.end()
    rest = text[start:]
    next_header = re.search(r"^##\s+", rest, re.MULTILINE)
    section = rest[: next_header.start()] if next_header else rest
    return len(_BULLET_RE.findall(section))


def collect_story_file_stats(story_path: Path) -> dict[str, Any]:
    """Parse one story markdown file for #820 Oracle / Non-Oracle signals."""
    if not story_path.is_file():
        return {
            "path": str(story_path),
            "present": False,
            "has_oracle": False,
            "has_non_oracle": False,
            "covers_bullets": 0,
            "oracle_bullets": 0,
            "non_oracle_bullets": 0,
        }
    text = story_path.read_text(encoding="utf-8")
    return {
        "path": str(story_path),
        "present": True,
        "has_oracle": bool(_ORACLE_RE.search(text)),
        "has_non_oracle": bool(_NON_ORACLE_RE.search(text)),
        "covers_bullets": _section_bullet_count(text, _COVERS_RE),
        "oracle_bullets": _section_bullet_count(text, _ORACLE_RE),
        "non_oracle_bullets": _section_bullet_count(text, _NON_ORACLE_RE),
    }


def collect_stories_dir_stats(stories_dir: Path) -> dict[str, Any]:
    """Aggregate #820 template stats for a stories directory."""
    if not stories_dir.is_dir():
        return {
            "stories_dir": str(stories_dir),
            "stories_total": 0,
            "stories_with_oracle": 0,
            "stories_with_non_oracle": 0,
            "stories": [],
        }
    stories = sorted(stories_dir.glob("story__*.md"))
    per_file = [collect_story_file_stats(path) for path in stories]
    return {
        "stories_dir": str(stories_dir),
        "stories_total": len(per_file),
        "stories_with_oracle": sum(1 for s in per_file if s["has_oracle"]),
        "stories_with_non_oracle": sum(1 for s in per_file if s["has_non_oracle"]),
        "stories": per_file,
    }


def seed_story_from_prompt(
    *,
    prompt_path: Path,
    output_dir: Path,
    slug: str,
) -> dict[str, Any]:
    """Render canonical #820 story from a prompt without LLM (detect_change skipped)."""
    from pdd.user_story_tests import generate_user_story  # pylint: disable=import-outside-toplevel

    output_dir.mkdir(parents=True, exist_ok=True)
    with patch("pdd.user_story_tests.detect_change", return_value=([], 0.0, "")):
        success, message, cost, _model, story_file, linked = generate_user_story(
            prompt_files=[str(prompt_path.resolve())],
            stories_dir=str(output_dir),
            prompts_dir=str(prompt_path.parent.resolve()),
            output=str(output_dir / f"story__{slug}.md"),
        )
    story_path = Path(story_file) if story_file else output_dir / f"story__{slug}.md"
    stats = collect_story_file_stats(story_path) if success and story_path.is_file() else {}
    return {
        "success": success,
        "message": message,
        "cost_usd": cost,
        "story_path": str(story_path),
        "linked_prompts": linked,
        "template_stats": stats,
    }


def compare_story_arms(a0: dict[str, Any], a1: dict[str, Any]) -> dict[str, Any]:
    """Compare story template stats between A0- and A1-derived stories."""
    a0_stats = (a0.get("template_stats") or {}) if a0.get("success") else {}
    a1_stats = (a1.get("template_stats") or {}) if a1.get("success") else {}

    def _delta(key: str) -> Optional[int]:
        left = a0_stats.get(key)
        right = a1_stats.get(key)
        if isinstance(left, int) and isinstance(right, int):
            return right - left
        return None

    return {
        "a0_has_oracle": a0_stats.get("has_oracle"),
        "a1_has_oracle": a1_stats.get("has_oracle"),
        "a0_has_non_oracle": a0_stats.get("has_non_oracle"),
        "a1_has_non_oracle": a1_stats.get("has_non_oracle"),
        "delta_covers_bullets": _delta("covers_bullets"),
        "delta_oracle_bullets": _delta("oracle_bullets"),
        "delta_non_oracle_bullets": _delta("non_oracle_bullets"),
        "gained_oracle_section": (not a0_stats.get("has_oracle")) and bool(
            a1_stats.get("has_oracle")
        ),
    }
