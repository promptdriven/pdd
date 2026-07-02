"""Deterministic checks for unit-test-like user-story backfill."""

from __future__ import annotations

import hashlib
import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
STORIES_DIR = REPO_ROOT / "user_stories"
CONTRACTS_DIR = STORIES_DIR / "contracts"
PACKAGE_PROMPTS_DIR = REPO_ROOT / "pdd" / "prompts"
ISSUE_REF = "https://github.com/promptdriven/pdd/issues/1698"

STORY_PROMPTS_METADATA_RE = re.compile(
    r"<!--\s*pdd-story-prompts:\s*(?P<values>.*?)\s*-->",
    flags=re.IGNORECASE | re.DOTALL,
)
STORY_DEV_UNITS_METADATA_RE = re.compile(
    r"<!--\s*pdd-story-dev-units:\s*(?P<values>.*?)\s*-->",
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

UNIT_LIKE_STORIES = {
    "pdd_checkup_coverage_evidence": {
        "metadata_prompts": [
            "prompts/commands/checkup_python.prompt",
            "prompts/coverage_contracts_python.prompt",
            "prompts/contract_ir_python.prompt",
        ],
        "dev_units": [
            "checkup_python.prompt",
            "coverage_contracts_python.prompt",
            "contract_ir_python.prompt",
        ],
        "covers": {"R1", "R2", "R3", "R4", "R5"},
        "must_contain": (
            "Coverage reporting",
            "rule-to-evidence matrix",
        ),
    },
    "pdd_cli_mode_guardrails": {
        "metadata_prompts": [
            "prompts/core/cli_python.prompt",
            "prompts/commands/generate_python.prompt",
            "prompts/commands/modify_python.prompt",
            "prompts/commands/maintenance_python.prompt",
        ],
        "dev_units": [
            "cli_python.prompt",
            "generate_python.prompt",
            "modify_python.prompt",
            "maintenance_python.prompt",
        ],
        "covers": {"R1", "R2", "R3", "R4", "R5"},
        "must_contain": (
            "unit-test-like CLI regression",
            "invalid option combinations",
        ),
    },
    "pdd_contracts_check_gate": {
        "metadata_prompts": [
            "prompts/commands/contracts_python.prompt",
            "prompts/contract_check_python.prompt",
            "prompts/contract_ir_python.prompt",
        ],
        "dev_units": [
            "contracts_python.prompt",
            "contract_check_python.prompt",
            "contract_ir_python.prompt",
        ],
        "covers": {"R1", "R2", "R3", "R4", "R5"},
        "must_contain": (
            "deterministic contract-rule checker",
            "malformed or duplicate rule IDs",
        ),
    },
}


def _story_path(story_id: str) -> Path:
    return STORIES_DIR / f"story__{story_id}.md"


def _contract_path(story_id: str) -> Path:
    return CONTRACTS_DIR / f"{story_id}.contract.md"


def _parse_metadata(pattern: re.Pattern[str], story_text: str) -> list[str]:
    match = pattern.search(story_text)
    if not match:
        return []
    raw = match.group("values").strip()
    return [entry.strip() for entry in raw.split(",") if entry.strip()]


def _story_content_hash(story_text: str) -> str:
    without_prompt_meta = STORY_PROMPTS_METADATA_RE.sub("", story_text)
    without_meta = STORY_DEV_UNITS_METADATA_RE.sub("", without_prompt_meta)
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


def _prompt_package_path(metadata_prompt: str) -> Path:
    assert metadata_prompt.startswith("prompts/")
    return PACKAGE_PROMPTS_DIR / metadata_prompt.removeprefix("prompts/")


def test_unit_like_story_backfill_artifacts_are_complete() -> None:
    assert len(UNIT_LIKE_STORIES) == len(set(UNIT_LIKE_STORIES))

    for story_id, expected in UNIT_LIKE_STORIES.items():
        story_path = _story_path(story_id)
        contract_path = _contract_path(story_id)

        assert story_path.exists(), f"{story_id} story is missing"
        assert contract_path.exists(), f"{story_id} contract is missing"

        story_text = story_path.read_text(encoding="utf-8")
        contract_text = contract_path.read_text(encoding="utf-8")

        prompt_refs = _parse_metadata(STORY_PROMPTS_METADATA_RE, story_text)
        dev_units = _parse_metadata(STORY_DEV_UNITS_METADATA_RE, story_text)
        assert prompt_refs == expected["metadata_prompts"]
        assert dev_units == expected["dev_units"]
        assert len(prompt_refs) >= 2
        assert len(dev_units) >= 2

        for prompt_ref in prompt_refs:
            assert _prompt_package_path(prompt_ref).exists()
            assert f"`{prompt_ref}`" in contract_text

        header = _parse_contract_header(contract_text)
        assert header["derived-from-story"] == f"../story__{story_id}.md"
        assert header["story-hash"] == _story_content_hash(story_text)
        assert header["issue-ref"] == ISSUE_REF

        for section in REQUIRED_CONTRACT_SECTIONS:
            assert section in contract_text

        assert expected["covers"] <= _covered_rule_ids(contract_text)

        for phrase in expected["must_contain"]:
            assert phrase in contract_text
