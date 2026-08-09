"""Shared helpers for grounding metadata in llm_invoke and evidence manifests."""
from __future__ import annotations

import logging
import re
from typing import Any, Dict, List, Mapping, MutableMapping, Optional, Sequence

import click

logger = logging.getLogger(__name__)

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


def _example_module_slug(raw: Mapping[str, Any]) -> Optional[str]:
    """Return a stable module slug from a cloud examplesUsed record."""
    for key in ("module", "slug", "id"):
        value = raw.get(key)
        if value is not None and str(value).strip():
            return str(value).strip()
    return None


def selected_examples_from_cloud(examples_used: Any) -> List[Dict[str, Any]]:
    """Map a cloud examplesUsed array into evidence-manifest selected_examples entries.

    Preserves the cloud record shape (``id``, ``title``, hashes, similarity) while
    always emitting a stable ``module`` key for policy and display (module/slug/id).
    """
    if not isinstance(examples_used, list):
        return []

    selected: List[Dict[str, Any]] = []
    for raw in examples_used:
        if not isinstance(raw, dict):
            continue
        module = _example_module_slug(raw)
        if not module:
            continue
        entry: Dict[str, Any] = {"module": module}
        example_id = raw.get("id")
        title = raw.get("title")
        if example_id is not None and str(example_id).strip():
            entry["id"] = str(example_id).strip()
        if title is not None and str(title).strip():
            entry["title"] = str(title).strip()
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
            if not isinstance(item, dict):
                continue
            module = item.get("module") or item.get("id")
            if not module or not str(module).strip():
                continue
            normalized = dict(item)
            normalized["module"] = str(module).strip()
            selected.append(normalized)

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


def _pre_generation_accepts(decisions: Optional[Sequence[Any]]) -> set[str]:
    """Module slugs accepted during pre-generation --review-examples review."""
    accepted: set[str] = set()
    if not decisions:
        return accepted
    for item in decisions:
        if not isinstance(item, Mapping):
            continue
        if item.get("phase") != "pre" or item.get("decision") != "accept":
            continue
        module = item.get("module")
        if module is not None and str(module).strip():
            accepted.add(str(module).strip())
    return accepted


def reviewed_from_decisions(
    decisions: Optional[Sequence[Any]],
    *,
    examples_used: Any = None,
) -> bool:
    """True when every cloud example was pre-approved before generation.

    ``reviewed`` must not be set from post-generation interactive review. With
    ``examples_used`` omitted, returns False (no implicit accept on empty runs).
    """
    pre_accepted = _pre_generation_accepts(decisions)
    if not pre_accepted:
        return False

    if examples_used is None:
        return False

    if not isinstance(examples_used, list) or not examples_used:
        return False

    for raw in examples_used:
        if not isinstance(raw, dict):
            continue
        slug = _example_module_slug(raw)
        if not slug or slug not in pre_accepted:
            return False
    return True


def grounding_reviewed_for_manifest(
    cli_params: Mapping[str, Any],
    examples_used: Any,
) -> bool:
    """Whether generation.grounding.reviewed should be true for this run."""
    if not cli_params.get("review_examples"):
        return False
    return reviewed_from_decisions(
        cli_params.get("grounding_review_decisions"),
        examples_used=examples_used,
    )


def record_grounding_review_decision(
    ctx_obj: Optional[MutableMapping[str, Any]],
    *,
    module: str,
    decision: str,
    reason: Optional[str] = None,
    phase: str = "pre",
) -> None:
    """Append a review decision for evidence manifest provenance."""
    if ctx_obj is None:
        return
    bucket = ctx_obj.get("grounding_review_decisions")
    if bucket is None:
        bucket = []
        ctx_obj["grounding_review_decisions"] = bucket
    if not isinstance(bucket, list):
        return
    entry: Dict[str, Any] = {
        "module": module,
        "decision": decision,
        "phase": phase,
    }
    if reason:
        entry["reason"] = reason
    bucket.append(entry)


def review_pinned_examples_before_generation(
    ctx_obj: Optional[MutableMapping[str, Any]],
    prompt_text: str,
    *,
    force: bool = False,
    quiet: bool = False,
) -> None:
    """Review <pin> tags before cloud/local generation (--review-examples)."""
    if ctx_obj is None:
        return

    pinned, _ = _lists_from_overrides(extract_grounding_overrides(prompt_text))
    if not pinned:
        if not quiet:
            click.echo(
                "No <pin> tags to review before generation; "
                "generation.grounding.reviewed stays false unless every "
                "cloud-selected example was pre-approved via <pin>."
            )
        return

    for slug in pinned:
        if force:
            record_grounding_review_decision(
                ctx_obj,
                module=slug,
                decision="accept",
                reason="force",
                phase="pre",
            )
            continue

        if not quiet:
            click.echo(f"Pinned grounding example: {slug}")
        if click.confirm(
            "Approve this pinned example before generation?",
            default=True,
        ):
            record_grounding_review_decision(
                ctx_obj, module=slug, decision="accept", phase="pre"
            )
        else:
            record_grounding_review_decision(
                ctx_obj, module=slug, decision="reject", phase="pre"
            )
            raise click.UsageError(
                f"Pinned grounding example {slug!r} was rejected under --review-examples."
            )


def warn_cloud_examples_not_preapproved(
    examples_used: Any,
    decisions: Optional[Sequence[Any]],
    *,
    quiet: bool = False,
) -> None:
    """Warn when cloud returned examples that were not pre-approved via <pin>."""
    if quiet:
        return
    pre_accepted = _pre_generation_accepts(decisions)
    if not isinstance(examples_used, list):
        return
    missing: List[str] = []
    for raw in examples_used:
        if not isinstance(raw, dict):
            continue
        slug = _example_module_slug(raw)
        if slug and slug not in pre_accepted:
            missing.append(slug)
    if missing:
        click.echo(
            click.style(
                "Cloud grounding examples were not pre-approved before generation "
                f"({', '.join(missing)}); generation.grounding.reviewed=false. "
                "Add <pin> tags and re-run with --review-examples to record reviewed=true.",
                fg="yellow",
            )
        )


def review_grounding_examples_interactive(
    examples_used: Any,
    ctx_obj: Optional[MutableMapping[str, Any]],
    *,
    force: bool = False,
    quiet: bool = False,
    phase: str = "pre",
) -> None:
    """Interactively accept or reject grounding examples (pre-generation only)."""
    if ctx_obj is None:
        return

    if phase != "pre":
        raise ValueError("review_grounding_examples_interactive only supports phase='pre'")

    if not isinstance(examples_used, list) or not examples_used:
        if not quiet:
            click.echo("No grounding examples were selected for review.")
        return

    accepted = False
    for raw in examples_used:
        if not isinstance(raw, dict):
            continue
        module = _example_module_slug(raw) or "unknown"
        label = module
        title = raw.get("title")
        if title:
            label = f"{module} ({title})"

        if force:
            record_grounding_review_decision(
                ctx_obj,
                module=module,
                decision="accept",
                reason="force",
                phase="pre",
            )
            accepted = True
            continue

        if not quiet:
            click.echo(f"Grounding example: {label}")
        if click.confirm("Approve this example before generation?", default=True):
            record_grounding_review_decision(
                ctx_obj, module=module, decision="accept", phase="pre"
            )
            accepted = True
        else:
            record_grounding_review_decision(
                ctx_obj, module=module, decision="reject", phase="pre"
            )

    if not accepted:
        raise click.UsageError(
            "All grounding examples were rejected under --review-examples; aborting."
        )


def grounding_overrides_from_click_ctx() -> Optional[Dict[str, List[str]]]:
    """Read pin/exclude overrides stashed on the active Click context."""
    try:
        ctx = click.get_current_context(silent=True)
    except Exception:
        return None
    if not ctx or not isinstance(ctx.obj, dict):
        return None
    stored = ctx.obj.get("grounding_overrides")
    if isinstance(stored, dict):
        pinned, excluded = _lists_from_overrides(stored)
        return {"pinned": pinned, "excluded": excluded}
    return None


def reviewed_from_click_ctx(*, examples_used: Any = None) -> bool:
    """Return whether pre-generation review covers the examples used on this run."""
    try:
        ctx = click.get_current_context(silent=True)
    except Exception:
        return False
    if not ctx or not isinstance(ctx.obj, dict):
        return False
    if not ctx.obj.get("review_examples"):
        return False
    return reviewed_from_decisions(
        ctx.obj.get("grounding_review_decisions"),
        examples_used=examples_used,
    )


def resolve_grounding_overrides_for_invoke(
    grounding_overrides: Optional[Mapping[str, Sequence[str]]] = None,
    source_prompt: Optional[str] = None,
) -> Dict[str, List[str]]:
    """Resolve pin/exclude overrides for an llm_invoke call."""
    if grounding_overrides is not None:
        pinned, excluded = _lists_from_overrides(grounding_overrides)
        return {"pinned": pinned, "excluded": excluded}
    if source_prompt:
        return extract_grounding_overrides(source_prompt)
    from_ctx = grounding_overrides_from_click_ctx()
    if from_ctx is not None:
        return from_ctx
    return {"pinned": [], "excluded": []}


def stash_grounding_overrides_on_ctx(
    ctx_obj: Optional[MutableMapping[str, Any]],
    prompt_text: str,
) -> Dict[str, List[str]]:
    """Store extracted overrides on ctx.obj for downstream llm_invoke calls."""
    overrides = extract_grounding_overrides(prompt_text)
    if isinstance(ctx_obj, dict):
        ctx_obj["grounding_overrides"] = overrides
    return overrides


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
