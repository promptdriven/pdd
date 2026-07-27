"""Deterministic local planning for ordinary-language product intent."""
from __future__ import annotations

import hashlib
import json
import os
import re
import textwrap
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

from .architecture_registry import extract_modules, find_architecture_for_project

INTENT_PLAN_SCHEMA_VERSION = "pdd.intent.plan.v1"
_MAX_TARGETS = 5
_MAX_SCANNED_FILES = 10_000
_MAX_SCAN_DEPTH = 5
_EXCLUDED_DIRS = {
    ".git",
    ".hg",
    ".mypy_cache",
    ".pdd",
    ".pytest_cache",
    ".ruff_cache",
    ".tox",
    ".venv",
    "__pycache__",
    "build",
    "coverage",
    "dist",
    "env",
    "node_modules",
    "target",
    "vendor",
    "venv",
}
_SOURCE_SUFFIXES = {
    ".c",
    ".cc",
    ".cpp",
    ".cs",
    ".cxx",
    ".go",
    ".h",
    ".hpp",
    ".java",
    ".js",
    ".jsx",
    ".kt",
    ".m",
    ".php",
    ".py",
    ".rb",
    ".rs",
    ".scala",
    ".sh",
    ".swift",
    ".ts",
    ".tsx",
}
_STOP_WORDS = {
    "about",
    "after",
    "agent",
    "also",
    "and",
    "are",
    "been",
    "before",
    "being",
    "both",
    "but",
    "can",
    "change",
    "code",
    "could",
    "does",
    "during",
    "each",
    "every",
    "file",
    "files",
    "for",
    "from",
    "github",
    "had",
    "has",
    "have",
    "into",
    "issue",
    "its",
    "just",
    "language",
    "let",
    "local",
    "make",
    "module",
    "more",
    "most",
    "need",
    "never",
    "only",
    "ordinary",
    "other",
    "over",
    "pdd",
    "plan",
    "planning",
    "product",
    "project",
    "prompt",
    "same",
    "should",
    "some",
    "such",
    "than",
    "that",
    "the",
    "their",
    "them",
    "then",
    "there",
    "these",
    "this",
    "those",
    "use",
    "user",
    "very",
    "want",
    "was",
    "were",
    "what",
    "when",
    "where",
    "which",
    "while",
    "who",
    "will",
    "with",
    "without",
    "would",
}
_NEGATIVE_OR_INVARIANT_MARKERS = (
    "must ",
    "must not",
    "never",
    "always",
    "do not",
    "don't",
    "without",
    "unchanged",
)
_EXAMPLE_MARKERS = ("for example", "e.g.", "such as", "when ")


@dataclass(frozen=True)
class IntentTarget:
    """A conservatively discovered product area that may own the request."""

    product_area: str
    prompt_path: Optional[str]
    output_path: Optional[str]
    architecture_path: Optional[str]
    score: int
    matched_terms: Tuple[str, ...]


@dataclass(frozen=True)
class IntentPlan:
    """Read-only plan for routing one preserved product-intent request."""

    schema_version: str
    intent_id: str
    title: str
    original_request: str
    original_request_sha256: str
    source_kind: str
    source_ref: Optional[str]
    project_root: str
    project_exists: bool
    repository_root: Optional[str]
    scope_kind: str
    adoption_scenario: str
    project_kind: str
    pdd_signals: Tuple[str, ...]
    candidate_targets: Tuple[IntentTarget, ...]
    must_preserve: Tuple[str, ...]
    examples: Tuple[str, ...]
    story_recommended: bool
    story_reasons: Tuple[str, ...]
    recommended_workflow: str
    open_decisions: Tuple[str, ...]
    warnings: Tuple[str, ...]


@dataclass(frozen=True)
class _InventoryTarget:
    """Internal searchable representation of an architecture/prompt entry."""

    product_area: str
    prompt_path: Optional[str]
    output_path: Optional[str]
    architecture_path: Optional[str]
    identity_text: str
    prose_text: str


def _relative_display(path: Path, root: Path) -> str:
    try:
        return path.relative_to(root).as_posix()
    except ValueError:
        return str(path)


def _walk_project(root: Path) -> Tuple[List[Path], bool, List[Path], bool, bool]:
    """Return prompts, source presence, pddrc files, truncation, other content.

    "Other content" means visible files that are neither recognized source nor
    prompts. A directory full of documentation is not an empty greenfield
    project root, and treating it as one invites scaffolding into it.
    """
    prompts: List[Path] = []
    pddrc_files: List[Path] = []
    source_found = False
    other_content_found = False
    scanned = 0
    truncated = False

    for dirpath, dirnames, filenames in os.walk(root, followlinks=False):
        current = Path(dirpath)
        try:
            depth = len(current.relative_to(root).parts)
        except ValueError:
            continue
        dirnames[:] = sorted(
            name
            for name in dirnames
            if name not in _EXCLUDED_DIRS and not name.startswith(".venv")
        )
        if depth >= _MAX_SCAN_DEPTH:
            dirnames[:] = []

        for filename in sorted(filenames):
            scanned += 1
            if scanned > _MAX_SCANNED_FILES:
                truncated = True
                return (
                    prompts,
                    source_found,
                    pddrc_files,
                    truncated,
                    other_content_found,
                )
            path = current / filename
            if filename == ".pddrc":
                pddrc_files.append(path)
            if path.suffix == ".prompt":
                prompts.append(path)
            if path.suffix.lower() in _SOURCE_SUFFIXES:
                source_found = True
            elif path.suffix != ".prompt" and not filename.startswith("."):
                other_content_found = True

    return prompts, source_found, pddrc_files, truncated, other_content_found


def _containing_repository_root(project_root: Path) -> Optional[Path]:
    """Find the nearest lexical ancestor containing a Git worktree marker."""
    candidate = project_root
    while not candidate.exists() and candidate != candidate.parent:
        candidate = candidate.parent
    if candidate.is_file():
        candidate = candidate.parent
    for current in (candidate, *candidate.parents):
        if (current / ".git").exists():
            return current.resolve()
    return None


def _adoption_scenario(
    project_kind: str, scope_kind: str, project_exists: bool
) -> str:
    if project_kind == "existing_pdd":
        return (
            "existing_pdd_subproject_change"
            if scope_kind == "subproject"
            else "existing_pdd_change"
        )
    if project_kind == "conventional_brownfield":
        return (
            "existing_subproject_adoption"
            if scope_kind == "subproject"
            else "existing_project_adoption"
        )
    if scope_kind == "subproject":
        return "new_subproject_design"
    if not project_exists:
        return "new_project_design"
    return "new_project_design"


def _load_architecture_targets(
    root: Path, architecture_paths: Sequence[Path]
) -> Tuple[List[_InventoryTarget], List[str], set[str]]:
    targets: List[_InventoryTarget] = []
    warnings: List[str] = []
    represented_prompts: set[str] = set()

    for architecture_path in architecture_paths:
        display_architecture = _relative_display(architecture_path, root)
        try:
            data = json.loads(architecture_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            warnings.append(
                f"Could not read {display_architecture} as architecture JSON: {exc}"
            )
            continue

        modules = extract_modules(data)
        if not modules and data not in ([], {"modules": []}):
            warnings.append(
                f"{display_architecture} contains no recognized architecture modules."
            )
        for entry in modules:
            filename = str(entry.get("filename") or "").strip()
            filepath = str(entry.get("filepath") or "").strip()
            description = str(entry.get("description") or "").strip()
            reason = str(entry.get("reason") or "").strip()
            tags_value = entry.get("tags")
            tags = (
                [str(tag) for tag in tags_value if isinstance(tag, (str, int, float))]
                if isinstance(tags_value, list)
                else []
            )
            interface_value = entry.get("interface")
            interface_text = (
                json.dumps(interface_value, sort_keys=True)
                if isinstance(interface_value, dict)
                else ""
            )
            prompt_path = _resolve_declared_prompt(root, architecture_path, filename)
            if prompt_path:
                represented_prompts.add(prompt_path)
            product_area = _product_area(description, filepath, filename)
            targets.append(
                _InventoryTarget(
                    product_area=product_area,
                    prompt_path=prompt_path,
                    output_path=filepath or None,
                    architecture_path=display_architecture,
                    identity_text=" ".join((filename, filepath, " ".join(tags))),
                    prose_text=" ".join((description, reason, interface_text)),
                )
            )
    return targets, warnings, represented_prompts


def _resolve_declared_prompt(
    root: Path, architecture_path: Path, filename: str
) -> Optional[str]:
    if not filename:
        return None
    declared = Path(filename)
    candidates = [
        architecture_path.parent / "prompts" / declared,
        root / "prompts" / declared,
        architecture_path.parent / declared,
    ]
    for candidate in candidates:
        if candidate.is_file():
            return _relative_display(candidate, root)
    conventional = root / "prompts" / declared
    return _relative_display(conventional, root)


def _product_area(description: str, filepath: str, filename: str) -> str:
    if description:
        first_sentence = re.split(r"(?<=[.!?])\s+", description, maxsplit=1)[0]
        return textwrap.shorten(first_sentence, width=140, placeholder="...")
    seed = filepath or filename or "Unnamed product area"
    stem = Path(seed).stem
    stem = re.sub(
        r"_(python|typescript|javascript|rust|cpp|java|go|llm)$",
        "",
        stem,
        flags=re.IGNORECASE,
    )
    return re.sub(r"[_-]+", " ", stem).strip().title() or "Unnamed product area"


def _prompt_only_targets(
    root: Path, prompt_paths: Iterable[Path], represented: set[str]
) -> List[_InventoryTarget]:
    targets: List[_InventoryTarget] = []
    seen: set[str] = set()
    for prompt_path in prompt_paths:
        display = _relative_display(prompt_path, root)
        identity = display.casefold()
        if identity in seen or display in represented:
            continue
        seen.add(identity)
        targets.append(
            _InventoryTarget(
                product_area=_product_area("", "", prompt_path.name),
                prompt_path=display,
                output_path=None,
                architecture_path=None,
                identity_text=display,
                prose_text="",
            )
        )
    return targets


def _tokens(text: str) -> set[str]:
    values = set(_lexemes(text))
    return {
        token
        for token in values
        if (len(token) >= 3 or token in {"ai", "api", "ui"}) and token not in _STOP_WORDS
    }


def _lexemes(text: str) -> List[str]:
    return [
        token.casefold()
        for token in re.findall(
            r"[A-Za-z0-9]+", text.replace("_", " ").replace("-", " ")
        )
    ]


def _meaningful_phrases(text: str) -> set[str]:
    """Return adjacent two-word phrases with at least one target-specific word."""
    values = _lexemes(text)
    return {
        f"{first} {second}"
        for first, second in zip(values, values[1:])
        if (len(first) >= 3 or first in {"ai", "api", "ui"})
        and (len(second) >= 3 or second in {"ai", "api", "ui"})
        and not (first in _STOP_WORDS and second in _STOP_WORDS)
    }


def _candidate_targets(
    request: str, inventory: Sequence[_InventoryTarget]
) -> Tuple[IntentTarget, ...]:
    request_tokens = _tokens(request)
    request_phrases = _meaningful_phrases(request)
    candidates: List[IntentTarget] = []
    for item in inventory:
        identity_matches = request_tokens & _tokens(item.identity_text)
        prose_matches = request_tokens & _tokens(item.prose_text)
        identity_phrase_matches = request_phrases & _meaningful_phrases(
            item.identity_text
        )
        prose_phrase_matches = request_phrases & _meaningful_phrases(item.prose_text)
        matched = (
            identity_matches
            | prose_matches
            | identity_phrase_matches
            | prose_phrase_matches
        )
        score = (
            8 * len(identity_phrase_matches)
            + 6 * len(prose_phrase_matches)
            + 5 * len(identity_matches)
            + 2 * len(prose_matches)
        )
        if score <= 0 or (not identity_matches and len(prose_matches) < 2):
            continue
        candidates.append(
            IntentTarget(
                product_area=item.product_area,
                prompt_path=item.prompt_path,
                output_path=item.output_path,
                architecture_path=item.architecture_path,
                score=score,
                matched_terms=tuple(sorted(matched)),
            )
        )
    candidates.sort(
        key=lambda target: (
            -target.score,
            target.product_area.casefold(),
            target.prompt_path or "",
        )
    )
    if not candidates:
        return ()
    relative_cutoff = max(5, (candidates[0].score * 3 + 4) // 5)
    return tuple(
        candidate
        for candidate in candidates
        if candidate.score >= relative_cutoff
    )[:_MAX_TARGETS]


def _sentences(request: str) -> List[str]:
    return [
        sentence.strip()
        for sentence in re.split(r"(?<=[.!?])\s+|\n+", request)
        if sentence.strip()
    ]


def _marked_sentences(request: str, markers: Sequence[str]) -> Tuple[str, ...]:
    found: List[str] = []
    for sentence in _sentences(request):
        lowered = sentence.casefold()
        if any(marker in lowered for marker in markers):
            found.append(sentence)
        if len(found) == 5:
            break
    return tuple(found)


def _story_recommendation(request: str) -> Tuple[bool, Tuple[str, ...]]:
    lowered = request.casefold()
    reasons: List[str] = []
    if any(term in lowered for term in ("user", "customer", "operator", "engineer")):
        reasons.append("user-visible behavior")
    if any(term in lowered for term in ("end-to-end", "across ", "workflow", "multiple parts")):
        reasons.append("cross-part behavior")
    if any(term in lowered for term in ("regression", "used to", "must never return")):
        reasons.append("regression protection")
    if any(
        term in lowered
        for term in (
            "must not",
            "never",
            "security",
            "privacy",
            "data loss",
            "delete",
            "payment",
        )
    ):
        reasons.append("critical boundary")
    return bool(reasons), tuple(reasons)


def _infer_title(request: str) -> str:
    first = next((line.strip() for line in request.splitlines() if line.strip()), "Intent")
    first = re.sub(r"^[#*>\-\s]+", "", first).strip()
    return textwrap.shorten(first, width=72, placeholder="...") or "Intent"


def _slugify(value: str) -> str:
    slug = re.sub(r"[^a-z0-9]+", "-", value.casefold()).strip("-")
    return slug[:48] or "intent"


def build_intent_plan(
    request: str,
    project_root: Path,
    *,
    title: Optional[str] = None,
    source_kind: str = "inline",
    source_ref: Optional[str] = None,
) -> IntentPlan:
    """Build a deterministic, read-only intent plan from local project evidence."""
    retained_request = request.strip()
    if not retained_request:
        raise ValueError("Intent request must not be empty.")
    root = Path(project_root).expanduser().resolve()
    project_exists = root.exists()
    if project_exists and not root.is_dir():
        raise ValueError(f"Project root is not a directory: {project_root}")

    digest = hashlib.sha256(retained_request.encode("utf-8")).hexdigest()
    resolved_title = (title or "").strip() or _infer_title(retained_request)
    intent_id = f"{_slugify(resolved_title)}-{digest[:8]}"

    repository_root = _containing_repository_root(root)
    scope_kind = (
        "subproject"
        if repository_root is not None and repository_root != root
        else "repository"
    )
    architecture_paths = find_architecture_for_project(root) if project_exists else []
    if project_exists:
        (
            prompt_paths,
            source_found,
            pddrc_paths,
            scan_truncated,
            other_content_found,
        ) = _walk_project(root)
    else:
        prompt_paths, source_found, pddrc_paths = [], False, []
        scan_truncated, other_content_found = False, False
    architecture_targets, warnings, represented = _load_architecture_targets(
        root, architecture_paths
    )
    inventory = architecture_targets + _prompt_only_targets(
        root, prompt_paths, represented
    )
    candidates = _candidate_targets(retained_request, inventory)

    signals: List[str] = []
    signals.extend(_relative_display(path, root) for path in pddrc_paths)
    signals.extend(_relative_display(path, root) for path in architecture_paths)
    if prompt_paths:
        signals.append(f"{len(prompt_paths)} prompt file(s)")
    signals = list(dict.fromkeys(signals))
    if scan_truncated:
        warnings.append(
            f"Project scan stopped after {_MAX_SCANNED_FILES} files; evidence may be incomplete."
        )

    if signals:
        project_kind = "existing_pdd"
        workflow = "change_existing_pdd"
    elif source_found:
        project_kind = "conventional_brownfield"
        workflow = "characterize_then_adopt"
    else:
        project_kind = "greenfield"
        workflow = "design_greenfield"
    scenario = _adoption_scenario(project_kind, scope_kind, project_exists)

    constraints = _marked_sentences(retained_request, _NEGATIVE_OR_INVARIANT_MARKERS)
    examples = _marked_sentences(retained_request, _EXAMPLE_MARKERS)
    story_recommended, story_reasons = _story_recommendation(retained_request)

    open_decisions: List[str] = []
    if project_kind == "existing_pdd" and not candidates:
        open_decisions.append(
            "No affected product area could be identified confidently; the agent must "
            "inspect the prompt graph or propose a new area."
        )
    elif project_kind == "conventional_brownfield":
        open_decisions.append(
            "Decide which existing behavior must be characterized before PDD "
            "ownership is introduced."
        )
    elif project_kind == "greenfield":
        open_decisions.append(
            "Review the proposed technology choices and architecture before prompt generation."
        )
        if project_exists and other_content_found:
            open_decisions.append(
                "This existing directory holds files but no recognized source; confirm "
                "it is the intended project root before anything is generated into it."
            )
            warnings.append(
                "Project root already contains non-source files such as documentation. "
                "It is classified greenfield only because no recognized source was found."
            )
    if scope_kind == "subproject":
        open_decisions.append(
            "Confirm the subproject boundary and the integration checks required "
            "at the containing repository boundary."
        )
    if not examples:
        open_decisions.append(
            "No concrete example was stated; add one if different interpretations are possible."
        )

    return IntentPlan(
        schema_version=INTENT_PLAN_SCHEMA_VERSION,
        intent_id=intent_id,
        title=resolved_title,
        original_request=retained_request,
        original_request_sha256=digest,
        source_kind=source_kind,
        source_ref=source_ref,
        project_root=str(root),
        project_exists=project_exists,
        repository_root=str(repository_root) if repository_root else None,
        scope_kind=scope_kind,
        adoption_scenario=scenario,
        project_kind=project_kind,
        pdd_signals=tuple(signals),
        candidate_targets=candidates,
        must_preserve=constraints,
        examples=examples,
        story_recommended=story_recommended,
        story_reasons=story_reasons,
        recommended_workflow=workflow,
        open_decisions=tuple(open_decisions),
        warnings=tuple(warnings),
    )


def intent_plan_to_dict(plan: IntentPlan) -> Dict[str, Any]:
    """Return the stable JSON-serializable representation of an intent plan."""
    return {
        "schema_version": plan.schema_version,
        "intent_id": plan.intent_id,
        "title": plan.title,
        "original_request": plan.original_request,
        "original_request_sha256": plan.original_request_sha256,
        "source": {"kind": plan.source_kind, "ref": plan.source_ref},
        "project": {
            "root": plan.project_root,
            "exists": plan.project_exists,
            "kind": plan.project_kind,
            "repository_root": plan.repository_root,
            "scope_kind": plan.scope_kind,
            "adoption_scenario": plan.adoption_scenario,
            "pdd_signals": list(plan.pdd_signals),
        },
        "candidate_targets": [
            {
                "product_area": target.product_area,
                "prompt_path": target.prompt_path,
                "output_path": target.output_path,
                "architecture_path": target.architecture_path,
                "score": target.score,
                "matched_terms": list(target.matched_terms),
            }
            for target in plan.candidate_targets
        ],
        "review": {
            "must_preserve": list(plan.must_preserve),
            "examples": list(plan.examples),
            "open_decisions": list(plan.open_decisions),
        },
        "story": {
            "recommended": plan.story_recommended,
            "reasons": list(plan.story_reasons),
        },
        "recommended_workflow": plan.recommended_workflow,
        "warnings": list(plan.warnings),
        "capabilities": {
            "planning": True,
            "apply": False,
            "writes_project_files": False,
            "requires_github": False,
            "invokes_llm": False,
        },
    }


def _section_lines(items: Sequence[str], empty_message: str) -> List[str]:
    if not items:
        return [f"- {empty_message}"]
    return [f"- {item}" for item in items]


def render_review_card(plan: IntentPlan) -> str:
    """Render one plain-language review card for the product/domain human."""
    if plan.candidate_targets:
        change_lines = [
            "- Candidate impact: "
            + ", ".join(target.product_area for target in plan.candidate_targets)
        ]
        area_lines = [
            f"- {target.product_area} (candidate; matched: "
            f"{', '.join(target.matched_terms)})"
            for target in plan.candidate_targets
        ]
    elif plan.project_kind == "greenfield":
        change_lines = ["- A product architecture and prompt graph need to be proposed."]
        area_lines = ["- No product areas exist yet; architecture review comes first."]
    elif plan.project_kind == "conventional_brownfield":
        change_lines = [
            "- Existing behavior must be characterized before assigning PDD ownership."
        ]
        area_lines = ["- No PDD-owned product area has been established."]
    else:
        change_lines = [
            "- The affected PDD-owned area still needs repository inspection; none was guessed."
        ]
        area_lines = ["- No confident candidate yet."]

    proof_lines = [
        "- Preserve and run relevant existing tests before applying the change.",
        "- Add focused behavioral tests for accepted behavior and examples.",
    ]
    if plan.must_preserve:
        proof_lines.append("- Add negative checks for every accepted MUST/MUST-NOT boundary.")
    if plan.project_kind == "greenfield":
        proof_lines.append("- Verify one small end-to-end slice before broad generation.")

    story_text = (
        "Recommended because " + ", ".join(plan.story_reasons) + "."
        if plan.story_recommended
        else "Not automatically recommended from the current wording."
    )
    lines = [
        f"Intent plan: {plan.title}",
        f"Project state: {plan.project_kind}",
        f"Project scope: {plan.scope_kind} ({plan.adoption_scenario})",
        "",
        "What I heard:",
        plan.original_request,
        "",
        "What will change:",
        *change_lines,
        "",
        "What must stay unchanged:",
        *_section_lines(plan.must_preserve, "No explicit invariant was stated."),
        "",
        "Important examples:",
        *_section_lines(plan.examples, "No concrete example was stated."),
        "",
        "How we will prove it:",
        *proof_lines,
        "",
        "Affected product areas:",
        *area_lines,
        "",
        "Open decisions:",
        *_section_lines(plan.open_decisions, "None identified by deterministic planning."),
        "",
        "Story coverage:",
        f"- {story_text}",
    ]
    if plan.warnings:
        lines.extend(("", "Warnings:", *_section_lines(plan.warnings, "")))
    lines.extend(
        (
            "",
            "Planning only: no project files were changed, no GitHub access was used, "
            "and no model was invoked.",
        )
    )
    return "\n".join(lines)
