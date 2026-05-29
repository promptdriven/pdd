"""Shared helpers for grounding metadata in llm_invoke and evidence manifests."""
from __future__ import annotations

import re
from typing import Any, Dict, List, Mapping, Optional, Sequence

_PIN_RE = re.compile(r"<pin>([^<]+)</pin>", re.IGNORECASE)
_EXCLUDE_RE = re.compile(r"<exclude>([^<]+)</exclude>", re.IGNORECASE)


def extract_grounding_overrides(prompt_text: str) -> Dict[str, List[str]]:
    """Collect pin/exclude slugs from raw prompt text before preprocessing strips tags."""
    pinned = [match.strip() for match in _PIN_RE.findall(prompt_text or "") if match.strip()]
    excluded = [match.strip() for match in _EXCLUDE_RE.findall(prompt_text or "") if match.strip()]
    return {"pinned": pinned, "excluded": excluded}


def _lists_from_overrides(
    grounding_overrides: Optional[Mapping[str, Sequence[str]]],
) -> tuple[List[str], List[str]]:
    if not grounding_overrides:
        return [], []
    pinned_raw = grounding_overrides.get("pinned") or []
    excluded_raw = grounding_overrides.get("excluded") or []
    pinned = [str(item).strip() for item in pinned_raw if str(item).strip()]
    excluded = [str(item).strip() for item in excluded_raw if str(item).strip()]
    return pinned, excluded


def selected_examples_from_cloud(examples_used: Any) -> List[Dict[str, Any]]:
    """Map a cloud examplesUsed array into evidence-manifest selected_examples entries."""
    if not isinstance(examples_used, list):
        return []

    selected: List[Dict[str, Any]] = []
    for raw in examples_used:
        if not isinstance(raw, dict):
            continue
        module = raw.get("module") or raw.get("slug") or raw.get("id") or raw.get("title")
        if not module:
            continue
        entry: Dict[str, Any] = {"module": str(module)}
        prompt_hash = raw.get("prompt_sha256") or raw.get("promptSha256")
        code_hash = raw.get("code_sha256") or raw.get("codeSha256")
        similarity = raw.get("similarity")
        source = raw.get("source")
        if prompt_hash:
            entry["prompt_sha256"] = str(prompt_hash)
        if code_hash:
            entry["code_sha256"] = str(code_hash)
        if similarity is not None:
            try:
                entry["similarity"] = float(similarity)
            except (TypeError, ValueError):
                pass
        if source:
            entry["source"] = str(source)
        selected.append(entry)
    return selected


def build_grounding_metadata(
    *,
    mode: str,
    examples_used: Any = None,
    grounding_overrides: Optional[Mapping[str, Sequence[str]]] = None,
    reviewed: bool = False,
    selected_examples: Optional[Sequence[Mapping[str, Any]]] = None,
) -> Dict[str, Any]:
    """Build a generation.grounding object for evidence manifests and llm_invoke returns."""
    pinned, excluded = _lists_from_overrides(grounding_overrides)
    examples = (
        list(selected_examples)
        if selected_examples is not None
        else selected_examples_from_cloud(examples_used)
    )
    return {
        "mode": mode,
        "selected_examples": examples,
        "pinned": pinned,
        "excluded": excluded,
        "reviewed": bool(reviewed),
    }


def normalize_grounding(
    grounding: Optional[Mapping[str, Any]] = None,
    *,
    reviewed: bool = False,
) -> Dict[str, Any]:
    """Return a complete grounding object, defaulting to unavailable when absent."""
    if not grounding:
        return build_grounding_metadata(mode="unavailable", reviewed=reviewed)

    mode = grounding.get("mode") or "unavailable"
    selected_raw = grounding.get("selected_examples")
    selected: List[Dict[str, Any]] = []
    if isinstance(selected_raw, list):
        for item in selected_raw:
            if isinstance(item, dict) and item.get("module"):
                selected.append(dict(item))

    pinned, excluded = _lists_from_overrides(grounding)
    if not pinned and isinstance(grounding.get("pinned"), list):
        pinned = [str(item) for item in grounding["pinned"] if str(item).strip()]
    if not excluded and isinstance(grounding.get("excluded"), list):
        excluded = [str(item) for item in grounding["excluded"] if str(item).strip()]

    return {
        "mode": str(mode),
        "selected_examples": selected,
        "pinned": pinned,
        "excluded": excluded,
        "reviewed": bool(grounding.get("reviewed")) or reviewed,
    }


def grounding_from_llm_result(
    result: Optional[Mapping[str, Any]],
    *,
    grounding_overrides: Optional[Mapping[str, Sequence[str]]] = None,
    reviewed: bool = False,
) -> Dict[str, Any]:
    """Derive grounding metadata from an llm_invoke return dict."""
    if isinstance(result, Mapping) and isinstance(result.get("grounding"), Mapping):
        return normalize_grounding(result["grounding"], reviewed=reviewed)

    if isinstance(result, Mapping):
        examples_used = result.get("examplesUsed")
        if examples_used is not None:
            return build_grounding_metadata(
                mode="cloud",
                examples_used=examples_used,
                grounding_overrides=grounding_overrides,
                reviewed=reviewed,
            )

    pinned, excluded = _lists_from_overrides(grounding_overrides)
    return build_grounding_metadata(
        mode="unavailable",
        grounding_overrides={"pinned": pinned, "excluded": excluded},
        reviewed=reviewed,
    )


def reviewed_from_decisions(decisions: Optional[Sequence[Any]]) -> bool:
    """True when at least one --review-examples decision was recorded."""
    return bool(decisions)
