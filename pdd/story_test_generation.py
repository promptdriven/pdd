"""Deterministic pytest generation from user story files."""
from __future__ import annotations

import hashlib
import os
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

from .user_story_tests import _normalized_story_for_hash, story_id


_HEADING_RE = re.compile(r"^(?P<marks>#{2,6})\s+(?P<title>.+?)\s*$", re.MULTILINE)
_RULE_RE = re.compile(r"\bR-?\d+\b", re.IGNORECASE)


@dataclass(frozen=True)
class GeneratedStoryTest:
    """Result of generating one deterministic story-backed pytest file."""

    story_id: str
    story_file: Path
    test_file: Path
    story_hash: str
    changed: bool
    test_count: int

    def as_dict(self) -> dict[str, object]:
        return {
            "story_id": self.story_id,
            "story_file": str(self.story_file),
            "test_file": str(self.test_file),
            "story_hash": self.story_hash,
            "changed": self.changed,
            "test_count": self.test_count,
        }


def _contract_path_for_story(story_path: Path) -> Path:
    slug = story_id(story_path)
    return story_path.parent / "contracts" / f"{slug}.contract.md"


def _read_story_bundle(story_path: Path) -> tuple[str, Optional[Path], str]:
    story_text = story_path.read_text(encoding="utf-8")
    contract_path = _contract_path_for_story(story_path)
    if contract_path.exists():
        contract_text = contract_path.read_text(encoding="utf-8")
        return story_text, contract_path, f"{story_text}\n\n{contract_text}"
    return story_text, None, story_text


def _normalized_bundle(story_text: str, contract_path: Optional[Path]) -> str:
    """Return the story(+contract) bundle normalized for hashing.

    Both portions run through the canonical ``_normalized_story_for_hash`` so a
    metadata-only edit (relinking prompts/dev-units, which rewrites the
    ``<!-- pdd-story-prompts ... -->`` comments) does NOT change the hash
    (pdd#1889 Bug 2), while any change to the human-facing prose does. The
    contract stays part of the hash so a contract edit is still a change.
    """
    bundle = _normalized_story_for_hash(story_text)
    if contract_path is not None and contract_path.exists():
        try:
            contract_text = contract_path.read_text(encoding="utf-8")
        except OSError:
            return bundle
        bundle = f"{bundle}\n\n{_normalized_story_for_hash(contract_text)}"
    return bundle


def story_bundle_hash(story_path: Path) -> str:
    """Return the stable hash generated tests record for staleness checks.

    Normalized so a metadata-only prompt/dev-unit relink does not flip it
    (pdd#1889 Bug 2); see :func:`_normalized_bundle`.
    """
    story_text, contract_path, _ = _read_story_bundle(story_path)
    bundle = _normalized_bundle(story_text, contract_path)
    return hashlib.sha256(bundle.encode("utf-8")).hexdigest()[:16]


def _sections(markdown: str) -> dict[str, str]:
    matches = list(_HEADING_RE.finditer(markdown))
    result: dict[str, str] = {}
    for index, match in enumerate(matches):
        title = match.group("title").strip().lower()
        start = match.end()
        end = matches[index + 1].start() if index + 1 < len(matches) else len(markdown)
        result[title] = markdown[start:end].strip()
    return result


def _section(md_sections: dict[str, str], *names: str) -> str:
    for name in names:
        found = md_sections.get(name.lower())
        if found:
            return found
    return ""


def _bullets(text: str) -> list[str]:
    rows: list[str] = []
    for raw in text.splitlines():
        line = raw.strip()
        line = re.sub(r"^(?:[-*+]|\d+[.)])\s+", "", line).strip()
        if line:
            rows.append(line)
    return rows


def _literal_list(values: list[str], *, indent: str = "    ") -> str:
    if not values:
        return "[]"
    inner = ",\n".join(f"{indent}{value!r}" for value in values)
    return "[\n" + inner + "\n]"


def _test_name(slug: str, suffix: str) -> str:
    safe = re.sub(r"[^0-9a-zA-Z_]+", "_", slug).strip("_").lower() or "story"
    return f"test_story_{safe}_{suffix}"


def _default_output_for(story_path: Path) -> Path:
    root = story_path.parent.parent if story_path.parent.name == "user_stories" else Path.cwd()
    return root / "tests" / "story_regression" / f"test_story_{story_id(story_path)}.py"


def _resolve_output(story_path: Path, output: Optional[str]) -> Path:
    if not output:
        return _default_output_for(story_path)
    candidate = Path(output)
    if candidate.suffix == ".py":
        return candidate
    return candidate / f"test_story_{story_id(story_path)}.py"


def _relative_literal(target: Path, source_file: Path) -> str:
    return os.path.relpath(target.resolve(), source_file.parent.resolve())


def _render_test(
    *,
    slug: str,
    story_path: Path,
    contract_path: Optional[Path],
    output_path: Path,
    bundle_hash: str,
    oracle_items: list[str],
    negative_items: list[str],
    rule_ids: list[str],
) -> str:
    story_rel = _relative_literal(story_path, output_path)
    contract_rel = _relative_literal(contract_path, output_path) if contract_path else None
    oracle_name = _test_name(slug, "oracle_contract")
    negative_name = _test_name(slug, "negative_cases")
    rules_suffix = "_".join(rule_ids[:3]).replace("-", "").lower()
    if rules_suffix:
        oracle_name = _test_name(slug, f"{rules_suffix}_oracle_contract")

    oracle_list = _literal_list(oracle_items)
    negative_list = _literal_list(negative_items)
    lines = [
        '"""Generated story-backed regression tests.',
        "",
        "This file is deterministic and safe to run without LLM/cloud credentials.",
        '"""',
        "from pathlib import Path",
        "",
        "import pytest",
        "",
        f'PDD_STORY_ID = "{slug}"',
        f'PDD_STORY_HASH = "{bundle_hash}"',
        f'STORY_PATH = Path(__file__).resolve().parent / "{story_rel}"',
    ]
    if contract_rel:
        lines.append(f'CONTRACT_PATH = Path(__file__).resolve().parent / "{contract_rel}"')
    else:
        lines.append("CONTRACT_PATH = None")
    lines.extend(
        [
            "",
            "",
            "def _story_bundle() -> str:",
            "    story = STORY_PATH.read_text(encoding=\"utf-8\")",
            "    if CONTRACT_PATH is not None and CONTRACT_PATH.exists():",
            "        return story + \"\\n\\n\" + CONTRACT_PATH.read_text(encoding=\"utf-8\")",
            "    return story",
            "",
            "",
            "def _bundle_hash() -> str:",
            "    # Reuse the canonical primitive so the recorded PDD_STORY_HASH and",
            "    # the gate's freshness check can never drift (pdd#1889). A",
            "    # metadata-only prompt relink does not change this value.",
            "    from pdd.story_test_generation import story_bundle_hash",
            "",
            "    return story_bundle_hash(STORY_PATH)",
            "",
            "",
            "@pytest.mark.story(story_id=PDD_STORY_ID)",
            f"def {oracle_name}():",
            "    assert _bundle_hash() == PDD_STORY_HASH",
            f"    expected = {oracle_list}",
            "    bundle = _story_bundle()",
            "    assert expected, \"story has no Oracle or Acceptance Criteria clauses\"",
            "    for clause in expected:",
            "        assert clause in bundle",
            "",
        ]
    )
    if negative_items:
        lines.extend(
            [
                "",
                "@pytest.mark.story(story_id=PDD_STORY_ID)",
                f"def {negative_name}():",
                "    assert _bundle_hash() == PDD_STORY_HASH",
                f"    expected = {negative_list}",
                "    bundle = _story_bundle()",
                "    for clause in expected:",
                "        assert clause in bundle",
                "",
            ]
        )
    return "\n".join(lines) + "\n"


def _generate_behavioral_test(
    story_path: Path,
    output: Optional[str],
) -> GeneratedStoryTest:
    """Delegate to the entry-point (behavioral) generator and adapt its result.

    Used when the story's contract declares a ``## Entry Point``. The generated
    test imports the callable, invokes it (applying any ``## Seams``), and
    asserts the ``## Oracle`` / ``## Negative Cases`` expressions over the
    return value — a real behavioral oracle rather than a text pin.
    """
    from .story_test_generator import generate_story_test

    output_path = _resolve_output(story_path, output)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    before = output_path.read_text(encoding="utf-8") if output_path.exists() else None
    result = generate_story_test(story_path, output_path)
    after = result.output_path.read_text(encoding="utf-8")
    return GeneratedStoryTest(
        story_id=result.story_id,
        story_file=story_path,
        test_file=result.output_path,
        story_hash=result.story_hash,
        changed=before != after,
        test_count=result.test_count,
    )


def generate_story_regression_test(
    story_file: str | Path,
    *,
    output: Optional[str] = None,
) -> GeneratedStoryTest:
    """Generate or update a deterministic pytest regression file from a story."""
    story_path = Path(story_file)
    if not story_path.exists() or not story_path.is_file():
        raise FileNotFoundError(f'Story file not found: "{story_path}"')
    if not story_path.name.startswith("story__") or story_path.suffix.lower() != ".md":
        raise ValueError("Story path must be a story__*.md file")

    slug = story_id(story_path)
    story_text, contract_path, bundle = _read_story_bundle(story_path)
    md_sections = _sections(bundle)

    # If the contract declares a machine-readable ## Entry Point, generate a
    # *behavioral* test that calls the entry point and asserts the ## Oracle /
    # ## Negative Cases as Python expressions over `result` (delegating to
    # story_test_generator). Contracts without an Entry Point fall through to
    # the text-pinning generator below, which pins the story/contract clauses.
    # Route on heading PRESENCE, not truthiness: a declared but empty/partial
    # ## Entry Point must surface the behavioral generator's validation error
    # (missing `- module:`/`- callable:`) instead of silently degrading to a
    # text-pin that the user would mistake for a real behavioral oracle
    # (pdd#1889 C-F7). A contract with no ## Entry Point at all still falls
    # through to the text-pinning generator below.
    if "entry point" in md_sections:
        return _generate_behavioral_test(story_path, output)

    oracle_text = _section(md_sections, "Oracle", "Acceptance Criteria", "Story")
    negative_text = _section(md_sections, "Negative Cases", "Non-Oracle")
    covers_text = _section(md_sections, "Covers")
    oracle_items = _bullets(oracle_text)
    negative_items = _bullets(negative_text)
    rule_ids = sorted({match.group(0).upper().replace("-", "") for match in _RULE_RE.finditer(covers_text)})
    if not oracle_items:
        story_sections = _sections(story_text)
        oracle_items = _bullets(_section(story_sections, "Story"))
    if not oracle_items:
        # Refuse to emit a test whose only assertion is that the raw story text
        # contains itself — that is a tautology that can never catch a
        # regression. A malformed story (no ## Oracle / ## Acceptance Criteria /
        # ## Story clauses in the story or its contract) is a user error, not a
        # generation target.
        raise ValueError(
            f"Story {story_path.name} has no ## Oracle, ## Acceptance Criteria, "
            "or ## Story clauses to assert. Add at least a ## Story sentence "
            "(and ideally an ## Oracle / ## Acceptance Criteria contract) before "
            "generating a regression test."
        )

    output_path = _resolve_output(story_path, output)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    # Record the canonical (normalized) bundle hash, identical to what the gate
    # recomputes, so a metadata-only relink never falsely stales this test.
    bundle_hash = story_bundle_hash(story_path)
    rendered = _render_test(
        slug=slug,
        story_path=story_path,
        contract_path=contract_path,
        output_path=output_path,
        bundle_hash=bundle_hash,
        oracle_items=oracle_items,
        negative_items=negative_items,
        rule_ids=rule_ids,
    )
    existing = output_path.read_text(encoding="utf-8") if output_path.exists() else None
    changed = existing != rendered
    if changed:
        output_path.write_text(rendered, encoding="utf-8")
    return GeneratedStoryTest(
        story_id=slug,
        story_file=story_path,
        test_file=output_path,
        story_hash=bundle_hash,
        changed=changed,
        test_count=2 if negative_items else 1,
    )
