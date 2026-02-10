from __future__ import annotations

import os
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Tuple

from rich import print as rprint

from .detect_change import detect_change
from .get_extension import get_extension


DEFAULT_STORIES_DIR = "user_stories"
DEFAULT_PROMPTS_DIR = "prompts"
STORY_PREFIX = "story__"
STORY_SUFFIX = ".md"


def _resolve_stories_dir(stories_dir: Optional[str] = None) -> Path:
    resolved = stories_dir or os.environ.get("PDD_USER_STORIES_DIR") or DEFAULT_STORIES_DIR
    return Path(resolved)


def _resolve_prompts_dir(prompts_dir: Optional[str] = None) -> Path:
    resolved = prompts_dir or os.environ.get("PDD_PROMPTS_DIR") or DEFAULT_PROMPTS_DIR
    return Path(resolved)


def discover_story_files(stories_dir: Optional[str] = None) -> List[Path]:
    base_dir = _resolve_stories_dir(stories_dir)
    if not base_dir.exists() or not base_dir.is_dir():
        return []
    return sorted(p for p in base_dir.glob(f"{STORY_PREFIX}*{STORY_SUFFIX}") if p.is_file())


def discover_prompt_files(
    prompts_dir: Optional[str] = None,
    *,
    include_llm: bool = False,
) -> List[Path]:
    base_dir = _resolve_prompts_dir(prompts_dir)
    if not base_dir.exists() or not base_dir.is_dir():
        return []
    prompts = [p for p in base_dir.rglob("*.prompt") if p.is_file()]
    if not include_llm:
        prompts = [p for p in prompts if not p.name.lower().endswith("_llm.prompt")]
    return sorted(prompts)


def _read_story(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _build_prompt_name_map(prompt_files: Iterable[Path]) -> Dict[str, Path]:
    name_map: Dict[str, Path] = {}
    for pf in prompt_files:
        name_map[pf.name] = pf
        name_map[str(pf)] = pf
        name_map[pf.name.lower()] = pf
        name_map[str(pf).lower()] = pf
    return name_map


def _resolve_prompt_path(prompt_name: str, prompt_files: Iterable[Path]) -> Optional[Path]:
    name_map = _build_prompt_name_map(prompt_files)
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


def _prompt_to_code_path(prompt_path: Path, prompts_dir: Path) -> Optional[Path]:
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

    code_dir = prompts_dir.parent / "src"
    rel_dir = rel_path.parent
    if not extension:
        return None
    code_name = f"{basename_part}.{extension}"
    return (code_dir / rel_dir / code_name).resolve()


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
) -> Tuple[bool, List[Dict[str, object]], float, str]:
    """
    Run user story tests by calling detect_change on each story.

    A story passes if detect_change returns an empty changes_list.
    """
    prompt_files = prompt_files or discover_prompt_files(prompts_dir, include_llm=include_llm_prompts)
    story_files = story_files or discover_story_files(stories_dir)

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
        changes_list, cost, model = detect_change(
            [str(p) for p in prompt_files],
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

    ctx_obj = getattr(ctx, "obj", None) or {}
    original_skip = ctx_obj.get("skip_user_stories")
    ctx_obj["skip_user_stories"] = True
    setattr(ctx, "obj", ctx_obj)

    try:
        for change in changes_list:
            prompt_name = str(change.get("prompt_name") or "")
            prompt_path = _resolve_prompt_path(prompt_name, prompt_files)
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
            changed_files.append(str(prompt_path))
            if result_message.startswith("[bold red]Error"):
                errors.append(result_message)

    finally:
        if original_skip is None:
            ctx_obj.pop("skip_user_stories", None)
        else:
            ctx_obj["skip_user_stories"] = original_skip
        setattr(ctx, "obj", ctx_obj)

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
