"""User story discovery, validation, generation, and prompt-fix helpers."""
# pylint: disable=too-many-lines
from __future__ import annotations

import hashlib
import json
import logging
import os
import re
import subprocess
import sys
import tempfile
import warnings
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Tuple

from rich import print as rprint

from .detect_change import detect_change
from .get_extension import get_extension


DEFAULT_STORIES_DIR = "user_stories"
DEFAULT_PROMPTS_DIR = "prompts"
DEFAULT_SRC_DIR = "src"
_LANGUAGE_EXTENSION_FALLBACKS = {
    "python": ".py",
    "javascript": ".js",
    "typescript": ".ts",
    "java": ".java",
    "go": ".go",
    "ruby": ".rb",
    "rust": ".rs",
}
STORY_PREFIX = "story__"
STORY_SUFFIX = ".md"
# Two-file model: the human-verified Story lives at
# ``user_stories/story__<slug>.md``; the AI-generated, machine-checkable contract
# lives at ``user_stories/contracts/<slug>.contract.md``. The contract is derived
# from the human Story plus the original issue and regenerated when the Story
# changes. Keeping them in separate files keeps the human's sign-off tiny while
# the precise, evolving test contract is owned by the tooling.
CONTRACTS_SUBDIR = "contracts"
CONTRACT_SUFFIX = ".contract.md"
STORY_PROMPTS_METADATA_KEY = "pdd-story-prompts"
STORY_DEV_UNITS_METADATA_KEY = "pdd-story-dev-units"
STORY_PROMPTS_METADATA_RE = re.compile(
    r"<!--\s*pdd-story-prompts:\s*(?P<prompts>.*?)\s*-->",
    flags=re.IGNORECASE,
)
STORY_DEV_UNITS_METADATA_RE = re.compile(
    r"<!--\s*pdd-story-dev-units:\s*(?P<dev_units>.*?)\s*-->",
    flags=re.IGNORECASE,
)
STORY_PROMPT_REFERENCE_RE = re.compile(
    r"(?P<ref>[A-Za-z0-9_./-]+\.prompt)\b",
    flags=re.IGNORECASE,
)
logger = logging.getLogger(__name__)


def _resolve_stories_dir(
    stories_dir: Optional[str] = None,
    *,
    root: Optional[Path] = None,
) -> Path:
    """Resolve the directory containing story markdown files.

    When *root* is provided, relative paths (from the argument or from
    ``PDD_USER_STORIES_DIR``) are anchored to it so that callers invoked from
    outside the project directory still find the right location.
    """
    resolved = stories_dir or os.environ.get("PDD_USER_STORIES_DIR") or DEFAULT_STORIES_DIR
    p = Path(resolved)
    if root is not None and not p.is_absolute():
        return root / p
    return p


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


def parse_story_dev_unit_metadata(story_text: str) -> list[str]:
    """Extract dev-unit references from optional pdd-story-dev-units metadata."""
    match = STORY_DEV_UNITS_METADATA_RE.search(story_text)
    if not match:
        return []
    raw = match.group("dev_units").strip()
    if not raw:
        return []
    return [entry.strip() for entry in raw.split(",") if entry.strip()]


def get_all_dev_units_for_story(story_text: str) -> list[str]:
    """Return all dev units/prompts declared for a story, preserving order."""
    refs: list[str] = []
    seen: set[str] = set()
    for ref in parse_story_dev_unit_metadata(story_text) + _parse_story_prompt_metadata(story_text):
        key = ref.lower()
        if key in seen:
            continue
        seen.add(key)
        refs.append(ref)
    return refs


def story_is_cross_unit(story_text: str) -> bool:
    """Return True when a story declares two or more linked dev units/prompts."""
    return len(get_all_dev_units_for_story(story_text)) >= 2


def _dev_unit_ref_matches_prompt(ref: str, prompt_name: str) -> bool:
    """Return True when metadata reference *ref* points at *prompt_name*."""
    left = ref.lower()
    right = prompt_name.lower()
    return left == right or left.endswith("/" + right)


def get_cross_unit_stories_for_prompt(prompt_name: str, stories_dir: Path | str) -> list[dict]:
    """Return cross-unit stories that include *prompt_name* in their metadata."""
    root = Path(stories_dir)
    if not root.exists():
        return []

    matches: list[dict] = []
    for story_path in sorted(root.rglob(f"{STORY_PREFIX}*{STORY_SUFFIX}")):
        try:
            story_text = story_path.read_text(encoding="utf-8")
        except OSError:
            continue
        dev_units = get_all_dev_units_for_story(story_text)
        if len(dev_units) < 2:
            continue
        if not any(_dev_unit_ref_matches_prompt(ref, prompt_name) for ref in dev_units):
            continue
        matches.append(
            {
                "story": story_path.name,
                "story_id": story_id(story_path),
                "path": str(story_path),
                "dev_units": dev_units,
            }
        )
    return matches


def _prompt_reference_for_metadata(prompt_path: Path, prompts_dir: Optional[Path]) -> str:
    """Return a stable metadata reference for a prompt path."""
    if prompts_dir:
        try:
            return prompt_path.relative_to(prompts_dir).as_posix()
        except ValueError:
            pass
    return prompt_path.name


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

    if len(metadata_refs) >= 2:
        dev_units_line = f"<!-- {STORY_DEV_UNITS_METADATA_KEY}: {', '.join(metadata_refs)} -->"
        if STORY_DEV_UNITS_METADATA_RE.search(updated):
            updated = STORY_DEV_UNITS_METADATA_RE.sub(dev_units_line, updated, count=1)
        else:
            updated = updated.replace(metadata_line, f"{metadata_line}\n{dev_units_line}", 1)

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
    except (FileNotFoundError, ValueError):
        extension = _LANGUAGE_EXTENSION_FALLBACKS.get(language.lower(), "")
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


def cache_story_prompt_links(  # pylint: disable=too-many-arguments,too-many-locals,too-many-return-statements,too-many-branches
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

    explicit_prompt_files = list(prompt_files) if prompt_files else None
    prompt_files = prompt_files or discover_prompt_files(
        prompts_dir, include_llm=include_llm_prompts
    )
    if not prompt_files:
        return False, "No prompt files found to link user story metadata.", 0.0, "", []

    prompts_root = _resolve_prompts_dir(prompts_dir) if prompts_dir else None
    story_content = _read_story(story_path)

    # Explicit prompt inputs are authoritative: `pdd story link --prompt` and
    # `pdd story add --update` name the exact prompts to link, so honor them
    # all (merged with still-resolvable existing refs) without spending an LLM
    # call second-guessing the caller.
    if explicit_prompt_files and force_relink:
        existing_paths: List[Path] = []
        for ref in _parse_story_prompt_metadata(story_content):
            resolved = _resolve_prompt_path(ref, prompt_files, prompts_root)
            if resolved:
                existing_paths.append(resolved)
        linked_prompt_paths = _dedupe_prompt_paths(existing_paths + explicit_prompt_files)
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
        message = (
            "Story prompt metadata linked from explicit prompt inputs."
            if updated
            else "Story prompt metadata already up to date for explicit prompt inputs."
        )
        return True, message, 0.0, "", linked_refs

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

    detection_error = ""
    try:
        changes_list, cost, model = detect_change(
            [str(p) for p in prompt_files],
            story_content,
            strength,
            temperature,
            time,
            verbose=verbose,
        )
    except Exception as exc:  # pylint: disable=broad-exception-caught
        logger.warning("Story prompt detection failed; using deterministic links: %s", exc)
        changes_list = None
        cost = 0.0
        model = ""
        detection_error = str(exc)

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
        if detection_error:
            return (
                True,
                "Story prompt metadata linked by deterministic fallback after detection failed.",
                cost,
                model,
                linked_refs,
            )
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
    if detection_error:
        return (
            True,
            "Story prompt metadata already up to date by deterministic "
            "fallback after detection failed.",
            cost,
            model,
            linked_refs,
        )
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


# --- Issue-source resolution (issue #1356) -------------------------------
# User stories are authored from the GitHub ISSUE that motivates the work, not
# from the prompt. The issue is the behavioral source of truth; deriving the
# story from it (and never from prompt content) keeps the story an independent
# TDD oracle that can actually catch prompt regressions. An issue source may be
# a GitHub issue/PR URL, a bare or ``#``-prefixed issue number (resolved against
# the ``origin`` remote), or a path to a local markdown file.
_GITHUB_ISSUE_URL_RE = re.compile(
    r"^https?://github\.com/(?P<owner>[^/]+)/(?P<repo>[^/]+)/(?:issues|pull)/(?P<number>\d+)",
    re.IGNORECASE,
)
_ISSUE_NUMBER_RE = re.compile(r"^#?(?P<number>\d+)$")
_REMOTE_SLUG_RE = re.compile(r"github\.com[:/](?P<owner>[^/]+)/(?P<repo>[^/.]+)")


def _issue_title_from_markdown(text: str) -> Optional[str]:
    """Return the first level-1 markdown heading as a title, if present."""
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith("# "):
            return stripped[2:].strip() or None
    return None


def _infer_repo_slug() -> Optional[str]:
    """Infer ``owner/repo`` from the ``origin`` git remote, or None."""
    try:
        result = subprocess.run(
            ["git", "remote", "get-url", "origin"],
            capture_output=True,
            text=True,
            check=True,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    match = _REMOTE_SLUG_RE.search(result.stdout.strip())
    if not match:
        return None
    return f"{match.group('owner')}/{match.group('repo')}"


def _fetch_issue_via_gh(repo: str, number: str) -> Optional[Tuple[str, str]]:
    """Fetch ``(title, body)`` for an issue via the ``gh`` CLI, or None."""
    try:
        result = subprocess.run(
            ["gh", "issue", "view", number, "--repo", repo, "--json", "title,body"],
            capture_output=True,
            text=True,
            check=True,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    try:
        data = json.loads(result.stdout)
    except (ValueError, TypeError):
        return None
    title = str(data.get("title") or "").strip()
    body = str(data.get("body") or "").strip()
    if not title and not body:
        return None
    return title, body


def resolve_issue_source(  # pylint: disable=too-many-return-statements
    issue: str,
) -> Tuple[Optional[str], Optional[str], Optional[str]]:
    """Resolve an issue source to ``(title, body, ref)``.

    A local markdown file is preferred when the path exists (deterministic,
    offline). Otherwise a GitHub issue/PR URL or a bare/``#`` issue number is
    fetched via the ``gh`` CLI. Returns ``(None, None, None)`` when the source
    cannot be resolved so the caller can fail generation rather than author a
    story from nothing.
    """
    issue = (issue or "").strip()
    if not issue:
        return None, None, None

    candidate = Path(issue)
    if candidate.exists() and candidate.is_file():
        try:
            text = candidate.read_text(encoding="utf-8")
        except OSError:
            return None, None, None
        title = _issue_title_from_markdown(text) or candidate.stem
        return title, text, candidate.name

    url_match = _GITHUB_ISSUE_URL_RE.match(issue)
    if url_match:
        repo = f"{url_match.group('owner')}/{url_match.group('repo')}"
        number = url_match.group("number")
    else:
        number_match = _ISSUE_NUMBER_RE.match(issue)
        if not number_match:
            return None, None, None
        repo = _infer_repo_slug()
        if not repo:
            return None, None, None
        number = number_match.group("number")

    fetched = _fetch_issue_via_gh(repo, number)
    if fetched is None:
        return None, None, None
    title, body = fetched
    return title, body, f"{repo}#{number}"


_STORY_META_PROMPT_NAME = "generate_user_story_LLM"
_STORY_CONTRACT_PROMPT_NAME = "generate_story_contract_LLM"
# Two-file audience split (the human verifies the Story; the AI owns the
# contract). The human story file is tiny — it must carry the ``## Story``
# sentence and nothing else is required. Invalid or unavailable LLM output fails
# generation instead of writing a deterministic substitute, because a shallow
# deterministic story can miss prompt behavior and pass mutation tests that
# should fail.
_REQUIRED_STORY_SECTIONS = (
    "## Story",
)
# The generated contract file carries the machine-checkable sections plus a
# ``## Candidate Prompts`` list of other prompts the story could run against.
# These are top-level ``##`` headings because the contract is now its own file
# (the audience split is at the file level, not the heading level).
_REQUIRED_CONTRACT_SECTIONS = (
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
_PLACEHOLDER_TOKEN_RE = re.compile(
    r"<\s*(?:persona|capability|benefit|detail|state|action|behavior|"
    r"forbidden outcome[^>\n]*|what this story[^>\n]*)\s*>",
    re.IGNORECASE,
)
_PDD_METADATA_TAG_RE = re.compile(r"</?\s*pdd-(?:reason|interface|dependency)\b", re.IGNORECASE)
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


def _contains_placeholder_tokens(markdown: str) -> bool:
    """Return True when model output still contains template placeholders."""
    return bool(
        _PLACEHOLDER_TOKEN_RE.search(markdown)
        or _PDD_METADATA_TAG_RE.search(markdown)
    )


def _llm_generate_story_markdown(  # pylint: disable=too-many-arguments,too-many-locals,too-many-return-statements,broad-exception-caught,import-outside-toplevel
    *,
    title: str,
    issue_text: str,
    issue_ref: str,
    strength: float,
    temperature: float,
    time: float,
    verbose: bool,
) -> Tuple[Optional[str], float, str]:
    """Author a complete ``story__*.md`` body with the LLM (issue #1356).

    The model reads the GitHub ISSUE text -- never the prompt or generated code
    -- and writes the user story directly (persona / capability / benefit,
    Context, Acceptance Criteria, Negative Cases, etc.). Keeping prompt content
    out of this call is the whole point: the story stays an independent oracle,
    so it can fail when a prompt drifts away from the issue's intended behavior.
    The ``pdd-story-prompts`` metadata is stitched deterministically by the
    caller afterward, so story<->prompt linking and ``pdd detect --stories`` are
    unaffected by what the model emits.

    Returns ``(markdown, cost, model)``. Returns ``(None, cost, model)`` when the
    LLM is unavailable, errors, or returns markdown missing a required section.
    The caller treats that as a generation failure; it must not write a
    deterministic substitute story.
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
            "Meta-prompt %s not found; user-story generation cannot continue.",
            _STORY_META_PROMPT_NAME,
        )
        return None, 0.0, ""

    issue_block = f'<issue ref="{issue_ref}">\n{issue_text}\n</issue>'

    processed = preprocess(
        template,
        recursive=False,
        double_curly_brackets=True,
        exclude_keys=["STORY_TITLE", "ISSUE_TEXT"],
    )

    try:
        response = llm_invoke(
            prompt=processed,
            input_json={"STORY_TITLE": title, "ISSUE_TEXT": issue_block},
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose,
        )
    except Exception as exc:  # any provider/auth/network error -> generation failure
        logger.debug("User-story LLM generation failed: %s", exc)
        return None, 0.0, ""

    cost = float(response.get("cost", 0.0) or 0.0)
    model = response.get("model_name", "") or ""
    raw = response.get("result", "")
    if not isinstance(raw, str) or not raw.strip():
        logger.debug("User-story LLM returned empty output.")
        return None, cost, model

    markdown = _strip_markdown_code_fence(raw)
    missing = [section for section in _REQUIRED_STORY_SECTIONS if section not in markdown]
    if missing:
        logger.debug("LLM story missing required sections %s.", missing)
        return None, cost, model
    if _contains_placeholder_tokens(markdown):
        logger.debug("LLM story contains placeholder tokens.")
        return None, cost, model

    if not markdown.endswith("\n"):
        markdown += "\n"
    return markdown, cost, model


# ---------------------------------------------------------------------------
# AI contract file (derived from the human Story + issue)
# ---------------------------------------------------------------------------

_CONTRACT_HEADER_RE = re.compile(
    r"<!--\s*pdd-story-contract\b(?P<attrs>.*?)-->",
    flags=re.IGNORECASE | re.DOTALL,
)
_CONTRACT_ATTR_RE = re.compile(r"(?P<key>[a-z0-9_-]+)\s*=\s*\"(?P<val>[^\"]*)\"", re.IGNORECASE)


def _slug_from_story_path(story_path: Path) -> str:
    """Return the ``<slug>`` portion of a ``story__<slug>.md`` filename."""
    name = story_path.name
    if name.startswith(STORY_PREFIX):
        name = name[len(STORY_PREFIX):]
    if name.endswith(STORY_SUFFIX):
        name = name[: -len(STORY_SUFFIX)]
    return name


def story_id(path: "str | Path") -> str:
    """Return the canonical ``story_id`` (the ``<slug>``) for a story file path.

    This is the single, public identity helper shared across PDD: a
    ``user_stories/story__<slug>.md`` path maps to ``<slug>``. Accepts either a
    ``str`` or a :class:`pathlib.Path`. The mapping is byte-identical to the
    internal :func:`_slug_from_story_path` implementation, which this helper
    wraps; both the ``@pytest.mark.story`` marker mechanism (see
    ``pdd.story_regression``) and the on-disk story files therefore share one
    identity space.
    """
    return _slug_from_story_path(Path(path))


def _contract_path_for_story(story_path: Path) -> Path:
    """Return the sibling contract path for a human story file.

    ``user_stories/story__x.md`` -> ``user_stories/contracts/x.contract.md``.
    """
    slug = _slug_from_story_path(story_path)
    return story_path.parent / CONTRACTS_SUBDIR / f"{slug}{CONTRACT_SUFFIX}"


def _compose_story_oracle(story_path: Path, story_content: str) -> str:
    """Return the full detection oracle: human Story plus its generated contract.

    The human ``story__<slug>.md`` carries the prompt-link metadata and prose; the
    sibling ``contracts/<slug>.contract.md`` carries the machine-checkable
    acceptance criteria, negative cases, and oracle guidance the LLM detects
    against. Both ``run_user_story_tests`` (validation) and ``run_user_story_fix``
    (repair) must detect against the SAME combined oracle -- otherwise a fix
    derived from the tiny story alone loses the contract's acceptance criteria and
    can no-op or under-specify a change that later fails validation. When no
    contract exists yet, the story content is the oracle on its own.
    """
    contract_path = _contract_path_for_story(story_path)
    if contract_path.exists():
        try:
            return f"{story_content}\n\n{contract_path.read_text(encoding='utf-8')}"
        except OSError:
            return story_content
    return story_content


def _normalized_story_for_hash(story_text: str) -> str:
    """Return story text normalized for hashing.

    Drops story metadata comments and trailing whitespace so a metadata-only edit
    (e.g. relinking prompts/dev units) does not look like a Story change, while
    any edit to the human-facing prose does.
    """
    without_meta = STORY_PROMPTS_METADATA_RE.sub("", story_text)
    without_meta = STORY_DEV_UNITS_METADATA_RE.sub("", without_meta)
    lines = [line.rstrip() for line in without_meta.strip().splitlines()]
    return "\n".join(line for line in lines if line.strip())


def _story_content_hash(story_text: str) -> str:
    """Stable short hash of the human-facing story content."""
    norm = _normalized_story_for_hash(story_text)
    return hashlib.sha256(norm.encode("utf-8")).hexdigest()[:16]


def _parse_contract_header(contract_text: str) -> Dict[str, str]:
    """Parse the ``<!-- pdd-story-contract key="val" ... -->`` header attrs."""
    match = _CONTRACT_HEADER_RE.search(contract_text)
    if not match:
        return {}
    return {
        m.group("key").lower(): m.group("val")
        for m in _CONTRACT_ATTR_RE.finditer(match.group("attrs"))
    }


def _prompt_inventory_descriptor(prompt_path: Path) -> str:
    """Return a one-line descriptor for a prompt file (for the inventory)."""
    try:
        text = prompt_path.read_text(encoding="utf-8")
    except OSError:
        return ""
    reason = re.search(r"<pdd-reason>\s*(.*?)\s*</pdd-reason>", text, re.DOTALL | re.IGNORECASE)
    if reason:
        snippet = " ".join(reason.group(1).split())
    else:
        snippet = ""
        for line in text.splitlines():
            stripped = line.strip()
            if stripped and not stripped.startswith(("%", "<", "#")):
                snippet = stripped
                break
    return snippet[:160]


def _scan_prompt_inventory(
    prompts_dir: Optional[Path],
    *,
    extra_paths: Optional[Iterable[Path]] = None,
    include_llm: bool = False,
    limit: int = 60,
) -> List[Tuple[str, str]]:
    """Collect ``(relpath, descriptor)`` for candidate prompts in the codebase.

    The inventory feeds the contract generator so it can suggest other prompts
    this story could run against. Runtime ``*_LLM.prompt`` templates are excluded.
    """
    found: Dict[str, Path] = {}
    roots: List[Path] = []
    if prompts_dir is not None:
        roots.append(prompts_dir)
    for root in roots:
        if not root.exists() or not root.is_dir():
            continue
        for candidate in root.rglob("*.prompt"):
            if not candidate.is_file():
                continue
            if not include_llm and candidate.name.lower().endswith("_llm.prompt"):
                continue
            found[str(candidate.resolve()).lower()] = candidate
    for candidate in extra_paths or []:
        if candidate.is_file() and (include_llm or not candidate.name.lower().endswith("_llm.prompt")):
            found.setdefault(str(candidate.resolve()).lower(), candidate)

    base = prompts_dir.resolve() if prompts_dir else None
    inventory: List[Tuple[str, str]] = []
    for prompt_path in sorted(found.values(), key=lambda p: str(p).lower()):
        if base is not None:
            try:
                rel = prompt_path.resolve().relative_to(base).as_posix()
            except ValueError:
                rel = prompt_path.name
        else:
            rel = prompt_path.name
        inventory.append((rel, _prompt_inventory_descriptor(prompt_path)))
    return inventory[:limit]


def _llm_generate_story_contract(  # pylint: disable=too-many-arguments,too-many-locals,broad-exception-caught,import-outside-toplevel
    *,
    title: str,
    story_text: str,
    issue_text: str,
    inventory: List[Tuple[str, str]],
    primary_refs: List[str],
    strength: float,
    temperature: float,
    time: float,
    verbose: bool,
) -> Tuple[Optional[str], float, str]:
    """Author the machine-checkable contract from the human Story + issue.

    Returns ``(markdown, cost, model)`` or ``(None, cost, model)`` when the LLM is
    unavailable or returns a contract missing a required section.
    """
    try:
        from .llm_invoke import llm_invoke
        from .load_prompt_template import load_prompt_template
        from .preprocess import preprocess
    except Exception as exc:  # pragma: no cover - defensive import guard
        logger.debug("Contract LLM generation unavailable: %s", exc)
        return None, 0.0, ""

    template = load_prompt_template(_STORY_CONTRACT_PROMPT_NAME)
    if not template:
        logger.debug("Meta-prompt %s not found.", _STORY_CONTRACT_PROMPT_NAME)
        return None, 0.0, ""

    inventory_block = "\n".join(
        f"- {rel}" + (f" — {desc}" if desc else "") for rel, desc in inventory
    ) or "- (no other prompts found in the codebase)"
    primary_block = "\n".join(f"- {ref}" for ref in primary_refs) or "- (none)"

    processed = preprocess(
        template,
        recursive=False,
        double_curly_brackets=True,
        exclude_keys=[
            "STORY_TITLE",
            "STORY_TEXT",
            "ISSUE_TEXT",
            "PROMPT_INVENTORY",
            "PRIMARY_PROMPTS",
        ],
    )
    try:
        response = llm_invoke(
            prompt=processed,
            input_json={
                "STORY_TITLE": title,
                "STORY_TEXT": story_text,
                "ISSUE_TEXT": issue_text,
                "PROMPT_INVENTORY": inventory_block,
                "PRIMARY_PROMPTS": primary_block,
            },
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose,
        )
    except Exception as exc:
        logger.debug("Contract LLM generation failed: %s", exc)
        return None, 0.0, ""

    cost = float(response.get("cost", 0.0) or 0.0)
    model = response.get("model_name", "") or ""
    raw = response.get("result", "")
    if not isinstance(raw, str) or not raw.strip():
        return None, cost, model
    markdown = _strip_markdown_code_fence(raw)
    missing = [s for s in _REQUIRED_CONTRACT_SECTIONS if s not in markdown]
    if missing:
        logger.debug("LLM contract missing required sections %s.", missing)
        return None, cost, model
    if _contains_placeholder_tokens(markdown):
        logger.debug("LLM contract contains placeholder tokens.")
        return None, cost, model
    if not markdown.endswith("\n"):
        markdown += "\n"
    return markdown, cost, model


def _compose_contract_file(
    contract_body: str,
    *,
    title: str,
    story_rel: str,
    story_hash: str,
    issue_ref: str,
) -> str:
    """Wrap the contract body with the derived-from header used for sync."""
    header = (
        f'<!-- pdd-story-contract derived-from-story="{story_rel}" '
        f'story-hash="{story_hash}" issue-ref="{issue_ref}" -->\n'
    )
    notice = (
        "> Generated from the human-verified user story + issue. Do not hand-edit:\n"
        "> it is regenerated to align whenever the Story changes. Humans verify the\n"
        f"> Story (`{story_rel}`), not this contract.\n\n"
    )
    return f"{header}\n# Contract: {title}\n\n{notice}{contract_body}"


def _generate_and_write_contract(  # pylint: disable=too-many-arguments,too-many-locals
    *,
    story_path: Path,
    story_text: str,
    title: str,
    issue_text: str,
    issue_ref: str,
    prompts_root: Optional[Path],
    extra_prompt_paths: Iterable[Path],
    primary_refs: List[str],
    strength: float,
    temperature: float,
    time: float,
    verbose: bool,
) -> Tuple[Optional[Path], float, str, Optional[str]]:
    """Generate the contract for ``story_path`` and write it.

    Returns ``(contract_path, cost, model, error)``. ``contract_path`` is None and
    ``error`` is set when contract generation could not be completed.
    """
    inventory = _scan_prompt_inventory(prompts_root, extra_paths=extra_prompt_paths)
    body, cost, model = _llm_generate_story_contract(
        title=title,
        story_text=story_text,
        issue_text=issue_text,
        inventory=inventory,
        primary_refs=primary_refs,
        strength=strength,
        temperature=temperature,
        time=time,
        verbose=verbose,
    )
    if body is None:
        return None, cost, model, "contract generation returned no valid contract"

    contract_path = _contract_path_for_story(story_path)
    contract_path.parent.mkdir(parents=True, exist_ok=True)
    # The contract lives one level down (contracts/); reference the story relative
    # to the contract so the link survives the stories dir being moved.
    rel_to_contract = os.path.relpath(story_path, contract_path.parent)
    contract_text = _compose_contract_file(
        body,
        title=title,
        story_rel=rel_to_contract,
        story_hash=_story_content_hash(story_text),
        issue_ref=issue_ref,
    )
    contract_path.write_text(contract_text, encoding="utf-8")
    return contract_path, cost, model, None


def sync_user_story_contract(  # pylint: disable=too-many-arguments,too-many-locals,too-many-return-statements
    story_path: str,
    *,
    issue: Optional[str] = None,
    prompts_dir: Optional[str] = None,
    strength: float = 0.2,
    temperature: float = 0.0,
    time: float = 0.25,
    verbose: bool = False,
    force: bool = False,
) -> Tuple[bool, str, float, str, str]:
    """Regenerate a story's contract when the human Story has changed.

    The human-verified Story is the source of truth: when it is edited, the
    contract is regenerated from the edited Story plus the original issue (the
    issue ref is read from the existing contract header, or may be passed via
    ``issue``). Returns ``(changed, message, cost, model, contract_path)``.
    """
    story_p = Path(story_path)
    if not story_p.exists():
        return False, f"Story file not found: {story_path}", 0.0, "", ""
    story_text = _read_story(story_p)
    contract_p = _contract_path_for_story(story_p)

    current_hash = _story_content_hash(story_text)
    issue_ref = issue
    if contract_p.exists():
        header = _parse_contract_header(contract_p.read_text(encoding="utf-8"))
        if not force and header.get("story-hash") == current_hash:
            return False, "Contract already aligned with the Story.", 0.0, "", str(contract_p)
        issue_ref = issue or header.get("issue-ref")

    if not issue_ref:
        return (
            False,
            (
                "Cannot regenerate contract: no issue reference recorded in the "
                "contract header and none provided. Pass issue=<url|number|path>."
            ),
            0.0,
            "",
            str(contract_p),
        )

    issue_title, issue_text, resolved_ref = resolve_issue_source(issue_ref)
    if issue_text is None:
        return (
            False,
            f"Could not resolve issue source '{issue_ref}' to regenerate the contract.",
            0.0,
            "",
            str(contract_p),
        )

    prompts_root = _resolve_prompts_dir(prompts_dir) if prompts_dir else None
    heading = _issue_title_from_markdown(story_text)
    if heading and heading.lower().startswith("user story:"):
        heading = heading.split(":", 1)[1].strip()
    title = heading or issue_title or _slug_from_story_path(story_p)
    primary_refs = _parse_story_prompt_metadata(story_text)
    contract_path, cost, model, error = _generate_and_write_contract(
        story_path=story_p,
        story_text=story_text,
        title=title,
        issue_text=issue_text,
        issue_ref=resolved_ref or issue_ref,
        prompts_root=prompts_root,
        extra_prompt_paths=[],
        primary_refs=primary_refs,
        strength=strength,
        temperature=temperature,
        time=time,
        verbose=verbose,
    )
    if contract_path is None:
        return False, f"Contract regeneration failed: {error}", cost, model, str(contract_p)
    return True, f"Regenerated contract: {contract_path}", cost, model, str(contract_path)


def generate_user_story(  # pylint: disable=too-many-arguments,too-many-locals,too-many-branches,too-many-statements,too-many-return-statements,unused-argument
    *,
    prompt_files: List[str],
    issue: Optional[str] = None,
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
    Generate a ``story__*.md`` file from a GitHub ISSUE (issue #1356).

    The story body is authored from the issue -- the behavioral source of truth
    -- and never from the prompt content. ``prompt_files`` are still required:
    they are the prompts the story validates and are linked via
    ``pdd-story-prompts`` metadata so the story is re-generated/re-checked when
    those prompts (and their issue) change. Keeping prompt content out of story
    authoring is what makes the story an independent TDD oracle.

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

    if not issue:
        return (
            False,
            (
                "User story generation derives the story from a GitHub issue, not "
                "from prompt content. Provide an issue source with "
                "--issue <url|number|path-to-issue.md>."
            ),
            0.0,
            "",
            "",
            [],
        )

    prompts_root = _resolve_prompts_dir(prompts_dir) if prompts_dir else None

    # Resolve the issue source (URL / number / local markdown) BEFORE any LLM
    # call. The issue -- not the prompt -- is the behavioral input.
    issue_title, issue_text, issue_ref = resolve_issue_source(issue)
    if issue_text is None:
        return (
            False,
            (
                f"Could not resolve issue source '{issue}'. Provide a GitHub issue "
                "URL, an issue number, or a path to a local issue markdown file."
            ),
            0.0,
            "",
            "",
            [],
        )

    title = issue_title or _story_title_from_prompts(resolved_paths)
    # Issue #1356: author the user story with the LLM from the ISSUE text only.
    # The prompt is deliberately withheld so the story is an independent oracle.
    # Do not fall back to deterministic story generation; a shallow deterministic
    # story can pass `pdd detect --stories` even after meaningful prompt drift,
    # so invalid/unavailable model output is a hard generation failure.
    story_markdown, story_cost, story_model = _llm_generate_story_markdown(
        title=title,
        issue_text=issue_text,
        issue_ref=issue_ref or issue,
        strength=strength,
        temperature=temperature,
        time=time,
        verbose=verbose,
    )
    if story_markdown is None:
        return (
            False,
            (
                "User story generation requires a valid LLM-authored story derived "
                "from the issue; the model was unavailable or returned invalid story "
                "markdown."
            ),
            story_cost,
            story_model,
            "",
            [],
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

    linked_refs = [
        _prompt_reference_for_metadata(path.resolve(), prompts_root)
        for path in resolved_paths
    ]
    latest_story = _read_story(output_path)
    _upsert_story_prompt_metadata(
        output_path,
        latest_story,
        [path.resolve() for path in resolved_paths],
        prompts_root,
    )

    total_cost = story_cost
    model_used = story_model
    status_message = (
        f"Generated story file: {output_path}. "
        "Story prompt metadata linked from prompt inputs."
    )

    # Generate the AI contract (machine-checkable oracle + candidate prompts)
    # from the human Story + issue. This is best-effort: a contract failure must
    # not block writing the human-verified Story, which is the source of truth and
    # can have its contract regenerated later via sync_user_story_contract().
    human_story_text = _read_story(output_path)
    # Record a re-resolvable issue reference so the contract can be regenerated
    # later (sync) from any working directory: absolutize a local issue path,
    # otherwise keep the URL/number form the user supplied.
    durable_issue_ref = os.path.abspath(issue) if issue and os.path.exists(issue) else issue
    contract_path, contract_cost, contract_model, contract_error = _generate_and_write_contract(
        story_path=output_path,
        story_text=human_story_text,
        title=title,
        issue_text=issue_text,
        issue_ref=durable_issue_ref,
        prompts_root=prompts_root,
        extra_prompt_paths=[p.resolve() for p in resolved_paths],
        primary_refs=linked_refs,
        strength=strength,
        temperature=temperature,
        time=time,
        verbose=verbose,
    )
    total_cost += contract_cost
    # The human Story is the primary artifact; report its model. Fall back to the
    # contract model only when the story model is unknown.
    model_used = model_used or contract_model
    if contract_path is not None:
        status_message += f" Generated contract file: {contract_path}."
    else:
        status_message += (
            f" Contract generation was skipped ({contract_error}); "
            "the Story is written and its contract can be generated later."
        )

    return (
        True,
        status_message,
        total_cost,
        model_used,
        str(output_path),
        linked_refs,
    )


_NONINTERACTIVE_TRUTHY = ("1", "true", "yes", "on")


def _story_validation_noninteractive() -> bool:
    """Return True when story validation must not start browser/device auth.

    Story validation calls ``detect_change`` -> ``llm_invoke`` -> cloud auth,
    which can otherwise reach an interactive GitHub device-login flow and block
    forever in an agent/CI shell (issue #1923). Returns False when the caller
    explicitly opts in via ``PDD_ALLOW_INTERACTIVE``; True when
    ``PDD_NO_INTERACTIVE`` is already truthy; otherwise True when stdin is not a
    TTY (the default for agent/CI shells). Any error reading ``isatty()`` is
    treated as non-interactive.
    """
    if os.environ.get("PDD_ALLOW_INTERACTIVE", "").strip().lower() in _NONINTERACTIVE_TRUTHY:
        return False
    if os.environ.get("PDD_NO_INTERACTIVE", "").strip().lower() in _NONINTERACTIVE_TRUTHY:
        return True
    try:
        return not sys.stdin.isatty()
    except Exception:  # noqa: BLE001 - a missing/broken stdin means non-interactive
        return True


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

    # Issue #1923: story validation triggers cloud auth via detect_change ->
    # llm_invoke. When it should not prompt a human (non-TTY agent/CI shell),
    # force PDD_NO_INTERACTIVE around each auth-sensitive call so the device-flow
    # guard and interactive API-key acquisition fail closed instead of opening a
    # GitHub device-login flow that blocks forever. This protects every caller of
    # this function (detect --stories, change, agentic change, drift), not just
    # the detect command. Forcing "1" (rather than skipping when a falsy value is
    # already present) closes the gap where PDD_NO_INTERACTIVE="0"/"" would leave
    # the downstream truthiness guard unset.
    scope_noninteractive = _story_validation_noninteractive()

    for story_path in story_files:
        story_content = _read_story(story_path)
        metadata_prompt_refs = _parse_story_prompt_metadata(story_content)
        # The oracle is the human Story PLUS its generated contract (when present).
        # The human file carries the prompt-link metadata; the contract carries the
        # machine-checkable acceptance criteria the LLM detects against.
        oracle_content = _compose_story_oracle(story_path, story_content)
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

        if scope_noninteractive:
            previous_no_interactive = os.environ.get("PDD_NO_INTERACTIVE")
            os.environ["PDD_NO_INTERACTIVE"] = "1"
        try:
            changes_list, cost, model = detect_change(
                [str(p) for p in story_prompt_files],
                oracle_content,
                strength,
                temperature,
                time,
                verbose=verbose,
            )
        except Exception as exc:  # noqa: BLE001 - story validation must fail closed
            all_passed = False
            error_message = (
                f"Story validation failed for {story_path}: {exc}. If this is an "
                "authentication/credential error, non-interactive CI/agent runs "
                "must provide model API credentials, set PDD_JWT_TOKEN for PDD "
                "Cloud, or run `pdd auth login` before validation so no "
                "browser/device login is required."
            )
            results.append({
                "story": str(story_path),
                "passed": False,
                "changes": [],
                "error": error_message,
            })
            if not quiet:
                rprint(f"[bold]FAIL[/bold] {story_path}")
                rprint(f"[red]{error_message}[/red]")
            if fail_fast:
                break
            continue
        finally:
            if scope_noninteractive:
                if previous_no_interactive is None:
                    os.environ.pop("PDD_NO_INTERACTIVE", None)
                else:
                    os.environ["PDD_NO_INTERACTIVE"] = previous_no_interactive
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
    # Detect and repair against the SAME oracle validation uses: the human Story
    # plus its generated contract. With the two-file story model, the tiny story
    # file alone omits the acceptance criteria/oracle, so `pdd fix` would no-op or
    # produce an under-specified change that later fails `run_user_story_tests`.
    oracle_content = _compose_story_oracle(story_path, story_content)
    changes_list, detect_cost, detect_model = detect_change(
        [str(p) for p in prompt_files],
        oracle_content,
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

    # change_main reads the change spec from a file, so the contract-aware oracle
    # has to reach it on disk. When a contract is present, write the combined
    # Story+contract to a temp file and feed that as the change prompt; otherwise
    # the story file itself is the full oracle and is passed directly.
    change_prompt_file = str(story_path)
    oracle_tmp_path: Optional[str] = None
    if oracle_content != story_content:
        tmp = tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            suffix=f"__{story_path.name}",
            prefix="pdd_story_oracle_",
            delete=False,
        )
        try:
            tmp.write(oracle_content)
        finally:
            tmp.close()
        oracle_tmp_path = tmp.name
        change_prompt_file = oracle_tmp_path

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
                change_prompt_file=change_prompt_file,
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
        if oracle_tmp_path:
            try:
                os.unlink(oracle_tmp_path)
            except OSError:
                pass

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
