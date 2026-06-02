"""User story discovery, validation, generation, and prompt-fix helpers."""
# pylint: disable=too-many-lines
from __future__ import annotations

import logging
import os
import re
import warnings
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Tuple

from rich import print as rprint

from .contract_ir import Rule, parse_prompt_contracts
from .detect_change import detect_change
from .get_extension import get_extension


DEFAULT_STORIES_DIR = "user_stories"
DEFAULT_PROMPTS_DIR = "prompts"
DEFAULT_SRC_DIR = "src"
STORY_PREFIX = "story__"
STORY_SUFFIX = ".md"
STORY_PROMPTS_METADATA_KEY = "pdd-story-prompts"
STORY_PROMPTS_METADATA_RE = re.compile(
    r"<!--\s*pdd-story-prompts:\s*(?P<prompts>.*?)\s*-->",
    flags=re.IGNORECASE,
)
STORY_PROMPT_REFERENCE_RE = re.compile(
    r"(?P<ref>[A-Za-z0-9_./-]+\.prompt)\b",
    flags=re.IGNORECASE,
)
_FORBIDDEN_MODAL_RE = re.compile(r"\b(?:MUST|SHALL|MAY)\s+NOT\b", re.IGNORECASE)
_FORBIDDEN_CLAUSE_RE = re.compile(
    r"\b(?:must|shall|may)\s+not\s+([^.\n]+)",
    re.IGNORECASE,
)
logger = logging.getLogger(__name__)


def _resolve_stories_dir(stories_dir: Optional[str] = None) -> Path:
    """Resolve the directory containing story markdown files."""
    resolved = stories_dir or os.environ.get("PDD_USER_STORIES_DIR") or DEFAULT_STORIES_DIR
    return Path(resolved)


def _resolve_prompts_dir(prompts_dir: Optional[str] = None) -> Path:
    """Resolve the directory containing prompt files."""
    resolved = prompts_dir or os.environ.get("PDD_PROMPTS_DIR") or DEFAULT_PROMPTS_DIR
    return Path(resolved)


def discover_story_files(stories_dir: Optional[str] = None) -> List[Path]:
    """Discover user story files matching story__*.md in the stories directory."""
    base_dir = _resolve_stories_dir(stories_dir)
    if not base_dir.exists() or not base_dir.is_dir():
        return []
    return sorted(p for p in base_dir.glob(f"{STORY_PREFIX}*{STORY_SUFFIX}") if p.is_file())


def discover_prompt_files(
    prompts_dir: Optional[str] = None,
    *,
    include_llm: bool = False,
) -> List[Path]:
    """Discover .prompt files from prompts_dir, optionally including *_llm.prompt."""
    base_dir = _resolve_prompts_dir(prompts_dir)
    if not base_dir.exists() or not base_dir.is_dir():
        return []
    prompts = [p for p in base_dir.rglob("*.prompt") if p.is_file()]
    if not include_llm:
        prompts = [p for p in prompts if not p.name.lower().endswith("_llm.prompt")]
    return sorted(prompts)


def _read_story(path: Path) -> str:
    """Read and return a story file as UTF-8 text."""
    return path.read_text(encoding="utf-8")


def _build_prompt_name_map(
    prompt_files: Iterable[Path],
    prompts_dir: Optional[Path] = None,
) -> Dict[str, Path]:
    """Build case-sensitive and case-insensitive lookup keys for prompt paths."""
    name_map: Dict[str, Path] = {}
    for prompt_path in prompt_files:
        name_map[prompt_path.name] = prompt_path
        name_map[str(prompt_path)] = prompt_path
        name_map[prompt_path.name.lower()] = prompt_path
        name_map[str(prompt_path).lower()] = prompt_path
        if prompts_dir:
            try:
                rel = prompt_path.relative_to(prompts_dir)
                rel_str = str(rel)
                rel_posix = rel.as_posix()
                name_map[rel_str] = prompt_path
                name_map[rel_str.lower()] = prompt_path
                name_map[rel_posix] = prompt_path
                name_map[rel_posix.lower()] = prompt_path
            except ValueError:
                continue
    return name_map


def _resolve_prompt_path(
    prompt_name: str,
    prompt_files: Iterable[Path],
    prompts_dir: Optional[Path] = None,
) -> Optional[Path]:
    """Resolve a prompt name or relative path to an existing prompt path."""
    name_map = _build_prompt_name_map(prompt_files, prompts_dir)
    if prompt_name in name_map:
        return name_map[prompt_name]
    lower = prompt_name.lower()
    if lower in name_map:
        return name_map[lower]
    # Fallback: match by basename if detect output used a short name
    for prompt_path in prompt_files:
        if prompt_path.name == prompt_name or prompt_path.name.lower() == lower:
            return prompt_path
    return None


def _parse_story_prompt_metadata(story_content: str) -> List[str]:
    """Extract prompt references from optional pdd-story-prompts metadata."""
    match = STORY_PROMPTS_METADATA_RE.search(story_content)
    if not match:
        return []
    raw = match.group("prompts").strip()
    if not raw:
        return []
    return [entry.strip() for entry in raw.split(",") if entry.strip()]


def _prompt_reference_for_metadata(prompt_path: Path, prompts_dir: Optional[Path]) -> str:
    """Return a stable metadata reference for a prompt path."""
    if prompts_dir:
        try:
            return prompt_path.relative_to(prompts_dir).as_posix()
        except ValueError:
            pass
    return prompt_path.name


def _cross_module_covers_ref(prompt_ref: str) -> str:
    """Normalize a prompt ref for cross-module ``## Covers`` lines (``prompts/...#R1``)."""
    normalized = prompt_ref.replace("\\", "/")
    if normalized.startswith("prompts/"):
        return normalized
    return f"prompts/{normalized}"


def _upsert_story_prompt_metadata(
    story_path: Path,
    story_content: str,
    linked_prompt_paths: List[Path],
    prompts_dir: Optional[Path],
) -> bool:
    """Insert or replace pdd-story-prompts metadata in a story file."""
    unique_sorted = sorted(
        {pf.resolve() for pf in linked_prompt_paths},
        key=lambda p: str(p).lower(),
    )
    if not unique_sorted:
        return False

    metadata_refs = [
        _prompt_reference_for_metadata(pf, prompts_dir)
        for pf in unique_sorted
    ]
    metadata_line = f"<!-- {STORY_PROMPTS_METADATA_KEY}: {', '.join(metadata_refs)} -->"
    if STORY_PROMPTS_METADATA_RE.search(story_content):
        updated = STORY_PROMPTS_METADATA_RE.sub(metadata_line, story_content, count=1)
    else:
        updated = f"{metadata_line}\n\n{story_content}"

    if updated == story_content:
        return False

    story_path.write_text(updated, encoding="utf-8")
    return True


def _dedupe_prompt_paths(prompt_paths: Iterable[Path]) -> List[Path]:
    """Preserve order while deduplicating prompt paths."""
    deduped: List[Path] = []
    seen_paths = set()
    for prompt_path in prompt_paths:
        key = str(prompt_path.resolve()).lower()
        if key in seen_paths:
            continue
        deduped.append(prompt_path)
        seen_paths.add(key)
    return deduped


def _extract_prompt_refs_from_story_text(story_content: str) -> List[str]:
    """Extract .prompt references from story markdown text."""
    refs: List[str] = []
    seen_refs = set()
    for match in STORY_PROMPT_REFERENCE_RE.finditer(story_content):
        ref = match.group("ref").strip()
        if not ref:
            continue
        key = ref.lower()
        if key in seen_refs:
            continue
        refs.append(ref)
        seen_refs.add(key)
    return refs


def _resolve_prompt_refs_to_paths(
    prompt_refs: List[str],
    prompt_files: List[Path],
    prompts_root: Optional[Path],
) -> List[Path]:
    """Resolve prompt references to known prompt file paths."""
    resolved_paths: List[Path] = []
    for ref in prompt_refs:
        resolved = _resolve_prompt_path(ref, prompt_files, prompts_root)
        if resolved:
            resolved_paths.append(resolved)
    return _dedupe_prompt_paths(resolved_paths)


def _resolve_src_dir(prompts_dir: Path) -> Path:
    """Resolve source directory from PDD_SRC_DIR or default to ../src from prompts_dir."""
    resolved = os.environ.get("PDD_SRC_DIR")
    if resolved:
        return Path(resolved)
    return prompts_dir.parent / DEFAULT_SRC_DIR


def _prompt_to_code_path(prompt_path: Path, prompts_dir: Path) -> Optional[Path]:
    """Map a prompt file path to its corresponding source file path."""
    prompt_path = prompt_path.resolve()
    prompts_dir = prompts_dir.resolve()
    try:
        rel_path = prompt_path.relative_to(prompts_dir)
    except ValueError:
        return None

    stem = rel_path.stem
    if "_" not in stem:
        return None

    basename_part, language = stem.rsplit("_", 1)
    try:
        extension = get_extension(language)
    except ValueError:
        return None
    extension = extension.lstrip(".")

    code_dir = _resolve_src_dir(prompts_dir)
    rel_dir = rel_path.parent
    if not extension:
        return None
    code_name = f"{basename_part}.{extension}"
    return (code_dir / rel_dir / code_name).resolve()


def _change_main_succeeded(result_message: object) -> bool:
    """
    change_main (non-CSV mode) reports success with:
    "Modified prompt saved to <path>".
    """
    return isinstance(result_message, str) and result_message.startswith(
        "Modified prompt saved to "
    )


def _linked_prompts_from_changes(
    changes_list: List[Dict[str, object]],
    prompt_files: List[Path],
    prompts_root: Optional[Path],
) -> List[Path]:
    """Resolve detect_change prompt names to existing prompt file paths."""
    linked_prompt_paths: List[Path] = []
    for change in changes_list:
        prompt_name = str(change.get("prompt_name") or "")
        resolved_prompt = _resolve_prompt_path(prompt_name, prompt_files, prompts_root)
        if resolved_prompt:
            linked_prompt_paths.append(resolved_prompt)
    return _dedupe_prompt_paths(linked_prompt_paths)


def _select_story_prompt_links(
    *,
    story_content: str,
    prompt_files: List[Path],
    prompts_root: Optional[Path],
    changes_list: Optional[List[Dict[str, object]]] = None,
) -> Tuple[List[Path], str]:
    """
    Select deterministic story prompt links.

    Priority:
    1) detect_change deltas
    2) explicit .prompt refs in story text
    3) all prompt files (full-project fallback)
    """
    if changes_list is not None:
        linked_from_changes = _linked_prompts_from_changes(changes_list, prompt_files, prompts_root)
        if linked_from_changes:
            return linked_from_changes, "detect_change"

    story_refs = _extract_prompt_refs_from_story_text(story_content)
    linked_from_story = _resolve_prompt_refs_to_paths(story_refs, prompt_files, prompts_root)
    if linked_from_story:
        return linked_from_story, "story_content"

    return _dedupe_prompt_paths(prompt_files), "all_prompts"


def cache_story_prompt_links(  # pylint: disable=too-many-arguments,too-many-locals,too-many-return-statements
    *,
    story_file: str,
    prompts_dir: Optional[str] = None,
    prompt_files: Optional[List[Path]] = None,
    strength: float = 0.2,
    temperature: float = 0.0,
    time: float = 0.25,
    verbose: bool = False,
    include_llm_prompts: bool = False,
    force_relink: bool = False,
) -> Tuple[bool, str, float, str, List[str]]:
    """
    Detect touched prompts for a story and cache pdd-story-prompts metadata.

    Returns:
        success flag, status message, cost, model name, and linked prompt refs.
    """
    story_path = Path(story_file)
    if not story_path.exists() or not story_path.is_file():
        return False, f"User story file not found: {story_file}", 0.0, "", []

    prompt_files = prompt_files or discover_prompt_files(
        prompts_dir, include_llm=include_llm_prompts
    )
    if not prompt_files:
        return False, "No prompt files found to link user story metadata.", 0.0, "", []

    prompts_root = _resolve_prompts_dir(prompts_dir) if prompts_dir else None
    story_content = _read_story(story_path)

    # Keep existing valid metadata unchanged unless force_relink is requested.
    existing_refs = _parse_story_prompt_metadata(story_content)
    if existing_refs and not force_relink:
        unresolved_refs: List[str] = []
        resolved_refs: List[str] = []
        for ref in existing_refs:
            resolved = _resolve_prompt_path(ref, prompt_files, prompts_root)
            if resolved:
                resolved_refs.append(_prompt_reference_for_metadata(resolved, prompts_root))
            else:
                unresolved_refs.append(ref)
        if resolved_refs and not unresolved_refs:
            return (
                True,
                "Story already contains prompt metadata.",
                0.0,
                "",
                sorted(set(resolved_refs)),
            )

    changes_list, cost, model = detect_change(
        [str(p) for p in prompt_files],
        story_content,
        strength,
        temperature,
        time,
        verbose=verbose,
    )

    linked_prompt_paths, link_source = _select_story_prompt_links(
        story_content=story_content,
        prompt_files=prompt_files,
        prompts_root=prompts_root,
        changes_list=changes_list,
    )

    updated = _upsert_story_prompt_metadata(
        story_path,
        story_content,
        linked_prompt_paths,
        prompts_root,
    )
    linked_refs = sorted(
        {
            _prompt_reference_for_metadata(path.resolve(), prompts_root)
            for path in linked_prompt_paths
        }
    )
    if updated:
        if link_source == "detect_change":
            return True, "Story prompt metadata linked.", cost, model, linked_refs
        if link_source == "story_content":
            return (
                True,
                "Story prompt metadata linked from story content.",
                cost,
                model,
                linked_refs,
            )
        return True, "Story prompt metadata linked to full prompt set.", cost, model, linked_refs
    if link_source == "detect_change":
        return True, "Story prompt metadata already up to date.", cost, model, linked_refs
    if link_source == "story_content":
        return (
            True,
            "Story prompt metadata already up to date from story content.",
            cost,
            model,
            linked_refs,
        )
    return (
        True,
        "Story prompt metadata already up to date for full prompt set.",
        cost,
        model,
        linked_refs,
    )


def _slugify_story_name(raw_name: str) -> str:
    """Convert a free-form story name into a safe story__*.md slug."""
    slug = re.sub(r"[^a-z0-9]+", "_", raw_name.lower()).strip("_")
    return slug or "new_story"


def _default_story_output_path(story_slug: str, stories_root: Path) -> Path:
    """Compute a non-colliding output path for a generated story file."""
    stem = _slugify_story_name(story_slug)
    candidate = stories_root / f"{STORY_PREFIX}{stem}{STORY_SUFFIX}"
    if not candidate.exists():
        return candidate

    index = 1
    while True:
        next_candidate = stories_root / f"{STORY_PREFIX}{stem}_{index}{STORY_SUFFIX}"
        if not next_candidate.exists():
            return next_candidate
        index += 1


def _prompt_topic_name(prompt_path: Path) -> str:
    """Extract a human-friendly topic name from a prompt filename."""
    stem = prompt_path.stem
    if "_" in stem:
        stem = stem.rsplit("_", 1)[0]
    cleaned = stem.replace("_", " ").replace("-", " ").strip()
    return cleaned or prompt_path.stem


def _story_title_from_prompts(prompt_paths: List[Path]) -> str:
    """Build a title from one or more prompt file names."""
    topic_names = [_prompt_topic_name(path).title() for path in prompt_paths]
    if not topic_names:
        return "Generated Story"
    if len(topic_names) == 1:
        return f"{topic_names[0]} Flow"
    if len(topic_names) == 2:
        return f"{topic_names[0]} and {topic_names[1]} Flow"
    return f"{topic_names[0]} and {len(topic_names) - 1} More Flow"


def _story_slug_from_prompts(prompt_paths: List[Path]) -> str:
    """Build a filesystem-safe slug from prompt file names."""
    topic_names = [_slugify_story_name(_prompt_topic_name(path)) for path in prompt_paths]
    merged = "_".join(name for name in topic_names[:3] if name)
    return merged or "generated_story"


def _prompt_summary_line(prompt_path: Path) -> str:
    """Extract a compact summary line from prompt content."""
    try:
        content = prompt_path.read_text(encoding="utf-8")
    except OSError:
        return "Prompt included in story scope."
    for raw_line in content.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        if line.startswith("%"):
            continue
        if line.startswith("#") and not line.startswith("##"):
            continue
        if len(line) > 140:
            return f"{line[:137].rstrip()}..."
        return line
    return "Prompt included in story scope."


def _summary_text_from_rule_line(text: str) -> str:
    """Extract display summary from a rule header or first block line."""
    id_prefix = re.match(r"^R-?\d+\s*[-:]\s*(.+)$", text, re.IGNORECASE)
    if id_prefix:
        return id_prefix.group(1).strip()
    return re.sub(r"^[^a-zA-Z0-9]+", "", text).strip()


def _rule_covers_summary(rule: Rule) -> str:
    """Return a short human-readable summary for a parsed contract rule."""
    summary = _summary_text_from_rule_line(rule.line.strip())
    if not summary and rule.block:
        first_line = rule.block.splitlines()[0].strip()
        summary = _summary_text_from_rule_line(first_line)
    if len(summary) > 120:
        return summary[:117].rstrip() + "..."
    return summary or rule.raw_id.upper()


def _seed_covers_from_prompts(
    prompt_paths: List[Path],
    prompts_root: Optional[Path],
) -> List[Tuple[str, str, str, str]]:
    """Seed Covers bullets from ``<contract_rules>`` via ``contract_ir.parse_prompt_contracts``."""
    seeded: List[Tuple[str, str, str, str]] = []
    for path in prompt_paths:
        if not path.exists() or not path.is_file():
            continue
        parsed = parse_prompt_contracts(path.resolve())
        if not parsed.rules:
            continue
        ref = _prompt_reference_for_metadata(path, prompts_root)
        for rule in parsed.rules:
            if rule.raw_id == "(unnumbered)":
                continue
            rule_id = rule.raw_id.upper()
            summary = _rule_covers_summary(rule)
            seeded.append((ref, rule_id, summary, rule.block))
    return seeded


def _seed_negative_cases_from_rules(
    rules: List[Tuple[str, str, str, str]],
) -> List[str]:
    """Extract forbidden outcomes from rules containing MUST/SHALL/MAY NOT."""
    negatives: List[str] = []
    for _, _, _, rule_text in rules:
        if not _FORBIDDEN_MODAL_RE.search(rule_text):
            continue
        match = _FORBIDDEN_CLAUSE_RE.search(rule_text)
        if not match:
            continue
        clause = match.group(1).strip()
        if not clause:
            continue
        cleaned = re.sub(r"^[^a-zA-Z0-9]+", "", clause).strip()
        if not cleaned:
            continue
        bullet = cleaned[0].upper() + cleaned[1:]
        if not bullet.endswith("."):
            bullet += "."
        negatives.append(bullet)
    deduped: List[str] = []
    seen: set[str] = set()
    for neg in negatives:
        key = neg.lower()
        if key in seen:
            continue
        seen.add(key)
        deduped.append(neg)
    return deduped


def _render_story_markdown_from_prompts(  # pylint: disable=too-many-locals
    *,
    title: str,
    prompt_paths: List[Path],
    prompts_root: Optional[Path],
) -> str:
    """Render canonical story markdown using prompt-file inputs."""
    metadata_refs = [
        _prompt_reference_for_metadata(path, prompts_root)
        for path in prompt_paths
    ]
    seeded_rules = _seed_covers_from_prompts(prompt_paths, prompts_root)
    covers_lines: List[str] = []
    if seeded_rules:
        # Cross-module Covers when the story scopes multiple prompt files.
        use_cross = len(prompt_paths) > 1
        for ref, rule_id, summary, _ in seeded_rules:
            if use_cross:
                cross_ref = _cross_module_covers_ref(ref)
                covers_lines.append(f"- {cross_ref}#{rule_id}: {summary}")
            else:
                covers_lines.append(f"- {rule_id}: {summary}")
    else:
        covers_lines.append(
            "- R1: Add contract rule IDs here after contracts are authored."
        )
    covers_block = "\n".join(covers_lines)

    negatives = _seed_negative_cases_from_rules(seeded_rules)
    if negatives:
        neg_block = "\n".join(f"- {neg}" for neg in negatives)
    else:
        neg_block = "- List forbidden outcomes this story protects against."

    context_lines = [
        "Describe relevant state, assumptions, fixtures, users, records, "
        "external services, or dependencies.",
        "",
        "This story covers the following prompt files:",
    ]
    for path in prompt_paths:
        ref = _prompt_reference_for_metadata(path, prompts_root)
        summary = _prompt_summary_line(path)
        context_lines.append(f"- `{ref}`: {summary}")
    context_block = "\n".join(context_lines)

    metadata_line = f"<!-- {STORY_PROMPTS_METADATA_KEY}: {', '.join(metadata_refs)} -->"
    return (
        f"{metadata_line}\n\n"
        f"# User Story: {title}\n\n"
        "## Covers\n\n"
        f"{covers_block}\n\n"
        "## Story\n\n"
        "As a <persona>,\n"
        "I want the scoped prompt capabilities to compose correctly,\n"
        "so that the full workflow works end-to-end.\n\n"
        "## Context\n\n"
        f"{context_block}\n\n"
        "## Acceptance Criteria\n\n"
        "1. Given behavior required by all listed prompts, when used together, "
        "then all components function correctly.\n"
        "2. Given `pdd detect --stories` is run, when analyzed, then it reports "
        "no required prompt changes.\n\n"
        "## Oracle\n\n"
        "These details matter for pass/fail:\n"
        "- error type\n"
        "- state transition\n"
        "- absence/presence of external call\n"
        "- emitted event\n"
        "- returned value shape\n\n"
        "## Non-Oracle\n\n"
        "These details should not matter:\n"
        "- private helper names\n"
        "- internal class structure\n"
        "- exact wording of non-user-facing messages\n"
        "- deterministic but irrelevant ordering\n\n"
        "## Negative Cases\n\n"
        f"{neg_block}\n\n"
        "## Non-Goals\n\n"
        "What this story explicitly does not cover.\n\n"
        "## Notes\n\n"
        "Links, edge cases, fixtures, rationale, or implementation hints.\n"
    )


_STORY_META_PROMPT_NAME = "generate_user_story_LLM"
# An LLM-authored story must contain at least these sections to be accepted;
# otherwise the caller falls back to the deterministic template so the file
# stays structurally valid for `pdd detect --stories` / `run_user_story_tests`.
_REQUIRED_STORY_SECTIONS = ("## Story", "## Acceptance Criteria")
_CODE_FENCE_RE = re.compile(
    r"^\s*```[A-Za-z0-9_-]*\s*\n(?P<body>.*?)\n```\s*$",
    re.DOTALL,
)


def _strip_markdown_code_fence(text: str) -> str:
    """Drop a single wrapping ```...``` fence if the model wrapped the file."""
    match = _CODE_FENCE_RE.match(text.strip())
    if match:
        return match.group("body").strip()
    return text.strip()


def _llm_generate_story_markdown(  # pylint: disable=too-many-arguments,too-many-locals,too-many-return-statements
    *,
    title: str,
    prompt_paths: List[Path],
    prompts_root: Optional[Path],
    strength: float,
    temperature: float,
    time: float,
    verbose: bool,
) -> Tuple[Optional[str], float, str]:
    """Author a complete ``story__*.md`` body with the LLM (issue #1356).

    The model reads the prompt file(s) and writes the user story directly --
    persona / capability / benefit, Context, Acceptance Criteria, Negative
    Cases, etc. The ``pdd-story-prompts`` metadata is stitched deterministically
    by the caller afterward, so story<->prompt linking and ``pdd detect
    --stories`` are unaffected by what the model emits.

    Returns ``(markdown, cost, model)``. Returns ``(None, cost, model)`` when the
    LLM is unavailable, errors, or returns markdown missing a required section,
    so the caller can fall back to the deterministic template -- keeping
    ``pdd test <*.prompt>`` working offline and in tests without a provider key.
    """
    try:  # lazy imports to avoid a top-of-module import cycle through llm_invoke
        from .llm_invoke import llm_invoke
        from .load_prompt_template import load_prompt_template
        from .preprocess import preprocess
    except Exception as exc:  # pragma: no cover - defensive import guard
        logger.debug("User-story LLM generation unavailable: %s", exc)
        return None, 0.0, ""

    template = load_prompt_template(_STORY_META_PROMPT_NAME)
    if not template:
        logger.debug(
            "Meta-prompt %s not found; using deterministic story template.",
            _STORY_META_PROMPT_NAME,
        )
        return None, 0.0, ""

    blocks: List[str] = []
    for path in prompt_paths:
        ref = _prompt_reference_for_metadata(path.resolve(), prompts_root)
        try:
            prompt_text = path.read_text(encoding="utf-8")
        except OSError as exc:
            logger.debug("Could not read prompt %s for story generation: %s", path, exc)
            return None, 0.0, ""
        blocks.append(f'<prompt ref="{ref}">\n{prompt_text}\n</prompt>')
    prompt_files_block = "\n\n".join(blocks)

    processed = preprocess(
        template,
        recursive=False,
        double_curly_brackets=True,
        exclude_keys=["STORY_TITLE", "PROMPT_FILES"],
    )

    try:
        response = llm_invoke(
            prompt=processed,
            input_json={"STORY_TITLE": title, "PROMPT_FILES": prompt_files_block},
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose,
        )
    except Exception as exc:  # any provider/auth/network error -> fall back
        logger.debug("User-story LLM generation failed: %s", exc)
        return None, 0.0, ""

    cost = float(response.get("cost", 0.0) or 0.0)
    model = response.get("model_name", "") or ""
    raw = response.get("result", "")
    if not isinstance(raw, str) or not raw.strip():
        logger.debug("User-story LLM returned empty output; using template.")
        return None, cost, model

    markdown = _strip_markdown_code_fence(raw)
    missing = [section for section in _REQUIRED_STORY_SECTIONS if section not in markdown]
    if missing:
        logger.debug("LLM story missing required sections %s; using template.", missing)
        return None, cost, model

    if not markdown.endswith("\n"):
        markdown += "\n"
    return markdown, cost, model


def generate_user_story(  # pylint: disable=too-many-arguments,too-many-locals,too-many-branches,too-many-statements
    *,
    prompt_files: List[str],
    output: Optional[str] = None,
    stories_dir: Optional[str] = None,
    prompts_dir: Optional[str] = None,
    strength: float = 0.2,
    temperature: float = 0.0,
    time: float = 0.25,
    verbose: bool = False,
    include_llm_prompts: bool = False,
) -> Tuple[bool, str, float, str, str, List[str]]:
    """
    Generate a story__*.md file from one or more prompt files.

    Returns:
        success flag, message, cost, model name, generated story path, linked prompt refs.
    """
    if not prompt_files:
        return False, "No prompt files provided for story generation.", 0.0, "", "", []

    resolved_paths: List[Path] = []
    seen_keys = set()
    for prompt_file in prompt_files:
        prompt_path = Path(prompt_file)
        if not prompt_path.exists() or not prompt_path.is_file():
            return False, f"Prompt file not found: {prompt_file}", 0.0, "", "", []
        if prompt_path.suffix.lower() != ".prompt":
            return False, f"Story generation requires .prompt files: {prompt_file}", 0.0, "", "", []
        key = str(prompt_path.resolve()).lower()
        if key in seen_keys:
            continue
        seen_keys.add(key)
        resolved_paths.append(prompt_path)

    prompts_root = _resolve_prompts_dir(prompts_dir) if prompts_dir else None
    title = _story_title_from_prompts(resolved_paths)
    # Issue #1356: author the user story with the LLM from the prompt content.
    # When the LLM is unavailable (no provider key, offline, error, or
    # structurally-invalid output), fall back to the deterministic
    # contract-aware template so `pdd test <*.prompt>` keeps working in CI and
    # tests. Either way the pdd-story-prompts metadata is stitched in below.
    story_markdown, story_cost, story_model = _llm_generate_story_markdown(
        title=title,
        prompt_paths=resolved_paths,
        prompts_root=prompts_root,
        strength=strength,
        temperature=temperature,
        time=time,
        verbose=verbose,
    )
    if story_markdown is None:
        story_markdown = _render_story_markdown_from_prompts(
            title=title,
            prompt_paths=resolved_paths,
            prompts_root=prompts_root,
        )

    if output:
        output_path = Path(output)
        if output_path.exists() and output_path.is_dir():
            story_slug = _story_slug_from_prompts(resolved_paths)
            output_path = output_path / f"{STORY_PREFIX}{story_slug}{STORY_SUFFIX}"
    else:
        stories_root = _resolve_stories_dir(stories_dir)
        stories_root.mkdir(parents=True, exist_ok=True)
        output_path = _default_story_output_path(
            _story_slug_from_prompts(resolved_paths), stories_root
        )

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(story_markdown, encoding="utf-8")

    linked_refs_from_input = [
        _prompt_reference_for_metadata(path.resolve(), prompts_root)
        for path in resolved_paths
    ]
    linked_refs = linked_refs_from_input
    total_cost = story_cost
    model_name = story_model

    # Generation-time auto-detection: run detect_change on the story and
    # cache detected prompt links into metadata for deterministic reruns.
    detected_pool = discover_prompt_files(prompts_dir, include_llm=include_llm_prompts)
    merged_pool: List[Path] = []
    seen_pool = set()
    for prompt_path in resolved_paths + detected_pool:
        key = str(prompt_path.resolve()).lower()
        if key in seen_pool:
            continue
        merged_pool.append(prompt_path)
        seen_pool.add(key)

    (
        detect_success,
        detect_message,
        detect_cost,
        detect_model,
        detected_links,
    ) = cache_story_prompt_links(
        story_file=str(output_path),
        prompts_dir=prompts_dir,
        prompt_files=merged_pool,
        strength=strength,
        temperature=temperature,
        time=time,
        verbose=verbose,
        include_llm_prompts=include_llm_prompts,
        force_relink=True,
    )
    total_cost += detect_cost
    model_name = detect_model or model_name

    if detect_success and detected_links:
        message_lower = detect_message.lower()
        if "full prompt set" not in message_lower and "story content" not in message_lower:
            linked_refs = detected_links
            status_message = (
                f"Generated story file: {output_path}. "
                "Story prompt metadata auto-detected from story content."
            )
        else:
            # Detection fell back to full-project or story-text refs.
            # Rewrite metadata to the explicit input prompts so the file
            # stays scoped to what the user asked for.
            linked_refs = linked_refs_from_input
            latest_story = _read_story(output_path)
            _upsert_story_prompt_metadata(
                output_path,
                latest_story,
                [path.resolve() for path in resolved_paths],
                prompts_root,
            )
            status_message = (
                f"Generated story file: {output_path}. "
                "Story prompt metadata linked from prompt inputs."
            )
    else:
        # Detection produced no touched prompts or could not update metadata.
        # Write metadata scoped to the explicit input prompts.
        linked_refs = linked_refs_from_input
        latest_story = _read_story(output_path)
        _upsert_story_prompt_metadata(
            output_path,
            latest_story,
            [path.resolve() for path in resolved_paths],
            prompts_root,
        )
        status_message = (
            f"Generated story file: {output_path}. "
            "Story prompt metadata linked from prompt inputs."
        )

    return (
        True,
        status_message,
        total_cost,
        model_name,
        str(output_path),
        linked_refs,
    )


def run_user_story_tests(  # pylint: disable=too-many-arguments,redefined-outer-name,too-many-locals,too-many-branches,too-many-statements
    *,
    prompts_dir: Optional[str] = None,
    stories_dir: Optional[str] = None,
    story_files: Optional[List[Path]] = None,
    prompt_files: Optional[List[Path]] = None,
    strength: float = 0.2,
    temperature: float = 0.0,
    time: float = 0.25,
    verbose: bool = False,
    quiet: bool = False,
    fail_fast: bool = False,
    include_llm_prompts: bool = False,
    cache_story_prompt_links: bool = False,
    link_story_prompt_metadata: Optional[bool] = None,
) -> Tuple[bool, List[Dict[str, object]], float, str]:
    """
    Run user story tests by calling detect_change on each story.

    A story passes if detect_change returns an empty changes_list.

    ``link_story_prompt_metadata`` is a deprecated alias for
    ``cache_story_prompt_links`` (main API). When both are passed,
    ``cache_story_prompt_links`` wins if it is true.
    """
    if link_story_prompt_metadata is not None:
        warnings.warn(
            "link_story_prompt_metadata is deprecated; use cache_story_prompt_links",
            DeprecationWarning,
            stacklevel=2,
        )
        if not cache_story_prompt_links:
            cache_story_prompt_links = link_story_prompt_metadata

    prompt_files = prompt_files or discover_prompt_files(
        prompts_dir, include_llm=include_llm_prompts
    )
    story_files = story_files or discover_story_files(stories_dir)
    prompts_root = _resolve_prompts_dir(prompts_dir) if prompts_dir else None

    if not story_files:
        return True, [], 0.0, ""
    if not prompt_files:
        msg = "No prompt files found to validate user stories."
        if not quiet:
            rprint(f"[bold yellow]{msg}[/bold yellow]")
        return False, [], 0.0, ""

    total_cost = 0.0
    model_name = ""
    results: List[Dict[str, object]] = []
    all_passed = True

    for story_path in story_files:
        story_content = _read_story(story_path)
        metadata_prompt_refs = _parse_story_prompt_metadata(story_content)
        story_prompt_files = prompt_files
        if metadata_prompt_refs:
            resolved_story_prompts: List[Path] = []
            unresolved_prompt_refs: List[str] = []
            for ref in metadata_prompt_refs:
                resolved = _resolve_prompt_path(ref, prompt_files, prompts_root)
                if resolved:
                    resolved_story_prompts.append(resolved)
                else:
                    unresolved_prompt_refs.append(ref)

            if unresolved_prompt_refs and not quiet:
                rprint(
                    "[yellow]Warning:[/yellow] Unresolved prompts in "
                    f"{story_path}: {', '.join(unresolved_prompt_refs)}"
                )
            if resolved_story_prompts:
                story_prompt_files = _dedupe_prompt_paths(resolved_story_prompts)
            else:
                all_passed = False
                results.append(
                    {
                        "story": str(story_path),
                        "passed": False,
                        "changes": [],
                        "error": "No prompts from pdd-story-prompts metadata could be resolved.",
                    }
                )
                if not quiet:
                    rprint(f"[bold]FAIL[/bold] {story_path}")
                if fail_fast:
                    break
                continue

        changes_list, cost, model = detect_change(
            [str(p) for p in story_prompt_files],
            story_content,
            strength,
            temperature,
            time,
            verbose=verbose,
        )
        total_cost += cost
        model_name = model or model_name
        passed = len(changes_list) == 0
        if not passed:
            all_passed = False
        results.append({
            "story": str(story_path),
            "passed": passed,
            "changes": changes_list,
        })

        if cache_story_prompt_links and not metadata_prompt_refs:
            linked_prompt_paths, _ = _select_story_prompt_links(
                story_content=story_content,
                prompt_files=prompt_files,
                prompts_root=prompts_root,
                changes_list=changes_list,
            )
            updated = _upsert_story_prompt_metadata(
                story_path,
                story_content,
                linked_prompt_paths,
                prompts_root,
            )
            if updated:
                logger.info("Updated story prompt metadata links for %s", story_path)

        if not quiet:
            status = "PASS" if passed else "FAIL"
            rprint(f"[bold]{status}[/bold] {story_path}")

        if fail_fast and not passed:
            break

    return all_passed, results, total_cost, model_name


def run_user_story_fix(  # pylint: disable=too-many-arguments,too-many-locals,too-many-branches
    *,
    ctx: object,
    story_file: str,
    prompts_dir: Optional[str] = None,
    strength: float = 0.2,
    temperature: float = 0.0,
    time: float = 0.25,
    budget: float = 5.0,
    verbose: bool = False,
    quiet: bool = False,
) -> Tuple[bool, str, float, str, List[str]]:
    """
    Attempt to fix prompts based on a single user story.

    This runs detect_change on the story, then applies changes to each affected
    prompt by calling change_main with the story as the change prompt.
    """
    from .change_main import change_main  # pylint: disable=import-outside-toplevel

    prompts_root = _resolve_prompts_dir(prompts_dir)
    prompt_files = discover_prompt_files(str(prompts_root))

    if not prompt_files:
        msg = "No prompt files found to apply user story fixes."
        return False, msg, 0.0, "", []

    story_path = Path(story_file)
    if not story_path.exists():
        return False, f"User story file not found: {story_file}", 0.0, "", []

    story_content = _read_story(story_path)
    changes_list, detect_cost, detect_model = detect_change(
        [str(p) for p in prompt_files],
        story_content,
        strength,
        temperature,
        time,
        verbose=verbose,
    )

    if not changes_list:
        return True, "No prompt changes needed for this user story.", detect_cost, detect_model, []

    total_cost = detect_cost
    model_name = detect_model
    changed_files: List[str] = []
    errors: List[str] = []

    ctx_obj = getattr(ctx, "obj", None)
    if ctx_obj is None:
        ctx_obj = {}
        ctx.obj = ctx_obj
    original_skip = ctx_obj.get("skip_user_stories")
    ctx_obj["skip_user_stories"] = True

    try:
        for change in changes_list:
            prompt_name = str(change.get("prompt_name") or "")
            prompt_path = _resolve_prompt_path(prompt_name, prompt_files, prompts_root)
            if not prompt_path:
                errors.append(f"Unable to resolve prompt path: {prompt_name}")
                continue

            code_path = _prompt_to_code_path(prompt_path, prompts_root)
            if not code_path or not code_path.exists():
                errors.append(f"Code file not found for prompt: {prompt_path}")
                continue

            result_message, cost, model = change_main(
                ctx=ctx,
                change_prompt_file=str(story_path),
                input_code=str(code_path),
                input_prompt_file=str(prompt_path),
                output=None,
                use_csv=False,
                budget=budget,
            )
            total_cost += cost
            model_name = model or model_name
            if _change_main_succeeded(result_message):
                changed_files.append(str(prompt_path))
            else:
                logger.debug("Story fix failed for %s: %s", prompt_path, result_message)
                errors.append(str(result_message))

    finally:
        if original_skip is None:
            ctx_obj.pop("skip_user_stories", None)
        else:
            ctx_obj["skip_user_stories"] = original_skip

    if errors:
        return False, "\n".join(errors), total_cost, model_name, changed_files

    # Re-run validation for just this story after applying changes
    passed, _, validation_cost, validation_model = run_user_story_tests(
        prompts_dir=str(prompts_root),
        story_files=[story_path],
        prompt_files=prompt_files,
        strength=strength,
        temperature=temperature,
        time=time,
        verbose=verbose,
        quiet=quiet,
        fail_fast=True,
    )
    total_cost += validation_cost
    if validation_model:
        model_name = validation_model

    if not passed:
        return (
            False,
            "User story still failing after prompt updates.",
            total_cost,
            model_name,
            changed_files,
        )

    return True, "User story prompts updated successfully.", total_cost, model_name, changed_files
