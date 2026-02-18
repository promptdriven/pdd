from __future__ import annotations

import logging
import os
import re
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Tuple

from rich import print as rprint

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
    for pf in prompt_files:
        name_map[pf.name] = pf
        name_map[str(pf)] = pf
        name_map[pf.name.lower()] = pf
        name_map[str(pf).lower()] = pf
        if prompts_dir:
            try:
                rel = pf.relative_to(prompts_dir)
                rel_str = str(rel)
                rel_posix = rel.as_posix()
                name_map[rel_str] = pf
                name_map[rel_str.lower()] = pf
                name_map[rel_posix] = pf
                name_map[rel_posix.lower()] = pf
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
    for pf in prompt_files:
        if pf.name == prompt_name or pf.name.lower() == lower:
            return pf
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


def _resolve_src_dir(prompts_dir: Path) -> Path:
    """Resolve source directory from PDD_SRC_DIR or default to ../src from prompts_dir."""
    resolved = os.environ.get("PDD_SRC_DIR")
    if resolved:
        return Path(resolved)
    return prompts_dir.parent / DEFAULT_SRC_DIR


def _prompt_to_code_path(prompt_path: Path, prompts_dir: Path) -> Optional[Path]:
    """Map a prompt file path to its corresponding source file path."""
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
    return isinstance(result_message, str) and result_message.startswith("Modified prompt saved to ")


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
    return linked_prompt_paths


def cache_story_prompt_links(
    *,
    story_file: str,
    prompts_dir: Optional[str] = None,
    prompt_files: Optional[List[Path]] = None,
    strength: float = 0.2,
    temperature: float = 0.0,
    time: float = 0.25,
    verbose: bool = False,
    include_llm_prompts: bool = False,
) -> Tuple[bool, str, float, str, List[str]]:
    """
    Detect touched prompts for a story and cache pdd-story-prompts metadata.

    Returns:
        success flag, status message, cost, model name, and linked prompt refs.
    """
    story_path = Path(story_file)
    if not story_path.exists() or not story_path.is_file():
        return False, f"User story file not found: {story_file}", 0.0, "", []

    prompt_files = prompt_files or discover_prompt_files(prompts_dir, include_llm=include_llm_prompts)
    if not prompt_files:
        return False, "No prompt files found to link user story metadata.", 0.0, "", []

    prompts_root = _resolve_prompts_dir(prompts_dir) if prompts_dir else None
    story_content = _read_story(story_path)

    # Keep existing valid metadata unchanged.
    existing_refs = _parse_story_prompt_metadata(story_content)
    if existing_refs:
        unresolved_refs: List[str] = []
        resolved_refs: List[str] = []
        for ref in existing_refs:
            resolved = _resolve_prompt_path(ref, prompt_files, prompts_root)
            if resolved:
                resolved_refs.append(_prompt_reference_for_metadata(resolved, prompts_root))
            else:
                unresolved_refs.append(ref)
        if resolved_refs and not unresolved_refs:
            return True, "Story already contains prompt metadata.", 0.0, "", sorted(set(resolved_refs))

    changes_list, cost, model = detect_change(
        [str(p) for p in prompt_files],
        story_content,
        strength,
        temperature,
        time,
        verbose=verbose,
    )

    linked_prompt_paths = _linked_prompts_from_changes(changes_list, prompt_files, prompts_root)
    if not linked_prompt_paths:
        return True, "No touched prompts detected for story metadata linking.", cost, model, []

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
        return True, "Story prompt metadata linked.", cost, model, linked_refs
    return True, "Story prompt metadata already up to date.", cost, model, linked_refs


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
    except Exception:
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


def _render_story_markdown_from_prompts(
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
    scope_lines = []
    for path in prompt_paths:
        ref = _prompt_reference_for_metadata(path, prompts_root)
        summary = _prompt_summary_line(path)
        scope_lines.append(f"- `{ref}`: {summary}")

    scope_block = "\n".join(scope_lines)
    return (
        f"# User Story: {title}\n\n"
        f"<!-- {STORY_PROMPTS_METADATA_KEY}: {', '.join(metadata_refs)} -->\n\n"
        "## Story\n"
        "As a user, I want the scoped prompt capabilities to compose correctly so that the full workflow works end-to-end.\n\n"
        "## Prompt Scope\n"
        f"{scope_block}\n\n"
        "## Acceptance Criteria\n"
        "- [ ] Behavior required by all listed prompts works when used together.\n"
        "- [ ] `pdd detect --stories` reports no required prompt changes for this story.\n"
    )


def generate_user_story(
    *,
    prompt_files: List[str],
    output: Optional[str] = None,
    stories_dir: Optional[str] = None,
    prompts_dir: Optional[str] = None,
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
        output_path = _default_story_output_path(_story_slug_from_prompts(resolved_paths), stories_root)

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(story_markdown, encoding="utf-8")
    linked_refs = [
        _prompt_reference_for_metadata(path.resolve(), prompts_root)
        for path in resolved_paths
    ]
    return (
        True,
        f"Generated story file: {output_path}. Story prompt metadata linked from prompt inputs.",
        0.0,
        "",
        str(output_path),
        linked_refs,
    )


def run_user_story_tests(
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
) -> Tuple[bool, List[Dict[str, object]], float, str]:
    """
    Run user story tests by calling detect_change on each story.

    A story passes if detect_change returns an empty changes_list.
    """
    prompt_files = prompt_files or discover_prompt_files(prompts_dir, include_llm=include_llm_prompts)
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
                # Preserve order while deduplicating exact paths
                deduped: List[Path] = []
                seen_paths = set()
                for pf in resolved_story_prompts:
                    key = str(pf.resolve()).lower()
                    if key in seen_paths:
                        continue
                    deduped.append(pf)
                    seen_paths.add(key)
                story_prompt_files = deduped
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

        if cache_story_prompt_links and not metadata_prompt_refs and changes_list:
            linked_prompt_paths = _linked_prompts_from_changes(
                changes_list,
                prompt_files,
                prompts_root,
            )
            if linked_prompt_paths:
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


def run_user_story_fix(
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
    from .change_main import change_main

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
        return False, "User story still failing after prompt updates.", total_cost, model_name, changed_files

    return True, "User story prompts updated successfully.", total_cost, model_name, changed_files
