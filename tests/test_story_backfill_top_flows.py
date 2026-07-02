"""Deterministic checks for the top-flow user-story backfill."""

from __future__ import annotations

import hashlib
import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
STORIES_DIR = REPO_ROOT / "user_stories"
CONTRACTS_DIR = STORIES_DIR / "contracts"
PACKAGE_PROMPTS_DIR = REPO_ROOT / "pdd" / "prompts"

STORY_PROMPTS_METADATA_RE = re.compile(
    r"<!--\s*pdd-story-prompts:\s*(?P<prompts>.*?)\s*-->",
    flags=re.IGNORECASE | re.DOTALL,
)
CONTRACT_HEADER_RE = re.compile(
    r"<!--\s*pdd-story-contract\b(?P<attrs>.*?)-->",
    flags=re.IGNORECASE | re.DOTALL,
)
CONTRACT_ATTR_RE = re.compile(
    r"(?P<key>[a-z0-9_-]+)\s*=\s*\"(?P<val>[^\"]*)\"",
    flags=re.IGNORECASE,
)

REQUIRED_CONTRACT_SECTIONS = (
    "## Covers",
    "## Context",
    "## Acceptance Criteria",
    "## Oracle",
    "## Non-Oracle",
    "## Negative Cases",
    "## Non-Goals",
    "## Candidate Prompts",
    "## Notes",
)

TOP_FLOW_STORIES = {
    "pdd_sync": {
        "metadata_prompt": "prompts/commands/maintenance_python.prompt",
        "package_prompt": "commands/maintenance_python.prompt",
        "covers": {"R1", "R2", "R3", "R4"},
        "must_contain": ("project-wide/global synchronization", "single-module"),
    },
}


def _story_path(story_id: str) -> Path:
    return STORIES_DIR / f"story__{story_id}.md"


def _contract_path(story_id: str) -> Path:
    return CONTRACTS_DIR / f"{story_id}.contract.md"


def _parse_story_prompts(story_text: str) -> list[str]:
    match = STORY_PROMPTS_METADATA_RE.search(story_text)
    if not match:
        return []
    raw = match.group("prompts").strip()
    return [entry.strip() for entry in raw.split(",") if entry.strip()]


def _story_content_hash(story_text: str) -> str:
    without_meta = STORY_PROMPTS_METADATA_RE.sub("", story_text)
    lines = [line.rstrip() for line in without_meta.strip().splitlines()]
    normalized = "\n".join(line for line in lines if line.strip())
    return hashlib.sha256(normalized.encode("utf-8")).hexdigest()[:16]


def _parse_contract_header(contract_text: str) -> dict[str, str]:
    match = CONTRACT_HEADER_RE.search(contract_text)
    assert match, "contract must include pdd-story-contract header"
    return {
        attr.group("key").lower(): attr.group("val")
        for attr in CONTRACT_ATTR_RE.finditer(match.group("attrs"))
    }


def _covered_rule_ids(contract_text: str) -> set[str]:
    return set(re.findall(r"^\s*-\s+(R\d+):", contract_text, flags=re.MULTILINE))


def test_top_flow_story_backfill_artifacts_are_complete() -> None:
    for story_id, expected in TOP_FLOW_STORIES.items():
        story_path = _story_path(story_id)
        contract_path = _contract_path(story_id)

        assert story_path.exists(), f"{story_id} story is missing"
        assert contract_path.exists(), f"{story_id} contract is missing"

        story_text = story_path.read_text(encoding="utf-8")
        contract_text = contract_path.read_text(encoding="utf-8")

        prompt_refs = _parse_story_prompts(story_text)
        assert prompt_refs == [expected["metadata_prompt"]]
        assert (PACKAGE_PROMPTS_DIR / expected["package_prompt"]).exists()

        header = _parse_contract_header(contract_text)
        assert header["derived-from-story"] == f"../story__{story_id}.md"
        assert header["story-hash"] == _story_content_hash(story_text)
        assert header["issue-ref"]

        for section in REQUIRED_CONTRACT_SECTIONS:
            assert section in contract_text

        assert expected["covers"] <= _covered_rule_ids(contract_text)
        assert f"`{expected['metadata_prompt']}`" in contract_text

        for phrase in expected["must_contain"]:
            assert phrase in contract_text
