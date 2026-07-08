"""`pdd story` command group for managing user-story regression inputs."""
from __future__ import annotations

import subprocess
from pathlib import Path
from typing import Optional

import click

from ..story_regression import build_story_map
from ..story_regression_gate import (
    STATUS_MISSING,
    STATUS_PASSING,
    STATUS_STALE,
    evaluate_story_regression,
)
from ..user_story_tests import (
    STORY_PREFIX,
    STORY_SUFFIX,
    _parse_story_prompt_metadata,
    _slugify_story_name,
    cache_story_prompt_links,
    discover_story_files,
    generate_user_story,
    story_id,
)


def _validate_title_for_slug(title: Optional[str]) -> None:
    """Reject title text that looks like a path rather than a story title."""
    if not title:
        return
    candidate = Path(title)
    if candidate.is_absolute() or ".." in candidate.parts or "/" in title or "\\" in title:
        raise click.ClickException("Story title must not contain path traversal or path separators.")


def _proposed_story_path(title: Optional[str], stories_dir: Path) -> Path:
    """Return the path a title would map to for dry-run and duplicate checks."""
    slug = _slugify_story_name(title or "new_story")
    return stories_dir / f"{STORY_PREFIX}{slug}{STORY_SUFFIX}"


def _story_slug_seed(title: Optional[str], inline_text: Optional[str]) -> Optional[str]:
    """Return the CLI-provided text that should control the output story slug."""
    if title:
        return title
    if inline_text:
        return inline_text[:48]
    return None


def _inline_source_path(text: str, title: Optional[str]) -> str:
    """Persist inline story source text as a local issue markdown file."""
    source_dir = Path(".pdd") / "story_sources"
    source_dir.mkdir(parents=True, exist_ok=True)
    slug = _slugify_story_name(title or text[:48] or "inline_story")
    path = source_dir / f"{slug}.md"
    heading = title or "Inline Story Source"
    path.write_text(f"# {heading}\n\n{text.strip()}\n", encoding="utf-8")
    return str(path)


def _git_repo_root(cwd: Path) -> Path:
    """Return the current git repository root or raise a Click error."""
    try:
        completed = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            cwd=cwd,
            check=True,
            text=True,
            capture_output=True,
        )
    except (FileNotFoundError, subprocess.CalledProcessError) as exc:
        raise click.ClickException(
            "Cannot use --from-changed-files outside a git repository."
        ) from exc
    return Path(completed.stdout.strip())


def _changed_prompt_files(cwd: Path) -> list[str]:
    """Return changed `.prompt` files from git status, including untracked files."""
    repo_root = _git_repo_root(cwd)
    try:
        completed = subprocess.run(
            ["git", "-C", str(repo_root), "status", "--porcelain=v1", "--untracked-files=all"],
            check=True,
            text=True,
            capture_output=True,
        )
    except subprocess.CalledProcessError as exc:
        raise click.ClickException("Could not enumerate changed files with git status.") from exc

    prompts: list[str] = []
    seen: set[str] = set()
    for line in completed.stdout.splitlines():
        if len(line) < 4:
            continue
        path_text = line[3:].strip()
        if " -> " in path_text:
            path_text = path_text.rsplit(" -> ", 1)[1].strip()
        if not path_text.endswith(".prompt"):
            continue
        prompt_path = repo_root / path_text
        key = str(prompt_path.resolve()).lower()
        if key in seen:
            continue
        seen.add(key)
        prompts.append(str(prompt_path))

    if not prompts:
        raise click.ClickException("No changed .prompt files found for --from-changed-files.")
    return prompts


def _validate_story_inside_user_stories(story_path: Path) -> None:
    """Reject story paths that do not live under a user_stories directory."""
    if "user_stories" not in story_path.resolve().parts:
        raise click.ClickException("Story file must be inside user_stories/.")


def resolve_prompt_path(
    project_root: Path,
    basename: str,
    manifest: object | None = None,  # pylint: disable=unused-argument
) -> Path | None:
    """Resolve a dev-unit name to a prompt file using local prompt filenames."""
    try:
        from ..source_set_model import resolve_devunit_prompts

        matches = resolve_devunit_prompts(basename, project_root)
        if matches:
            return matches[0]
    except click.ClickException:
        pass

    prompts_root = project_root / "prompts"
    candidates: list[str] = [basename]
    if not basename.endswith(".prompt"):
        candidates.extend(
            [
                f"{basename}.prompt",
                f"{basename}_python.prompt",
                f"{basename}_javascript.prompt",
                f"{basename}_typescript.prompt",
            ]
        )

    for candidate in candidates:
        direct = prompts_root / candidate
        if direct.is_file():
            return direct

    lowered = {candidate.lower() for candidate in candidates}
    if prompts_root.exists():
        for prompt_path in sorted(prompts_root.rglob("*.prompt")):
            if prompt_path.name.lower() in lowered or prompt_path.stem.lower() == basename.lower():
                return prompt_path
    return None


def _resolve_prompt_inputs(prompts: tuple[str, ...], devunits: tuple[str, ...]) -> list[str]:
    """Combine explicit prompt paths and dev-unit resolutions into prompt inputs."""
    resolved: list[str] = [str(Path(prompt)) for prompt in prompts]
    project_root = Path.cwd()
    for devunit in devunits:
        prompt_path = resolve_prompt_path(project_root, devunit)
        if prompt_path is None:
            raise click.ClickException(f"Could not resolve devunit '{devunit}' to a prompt file.")
        resolved.append(str(prompt_path))

    deduped: list[str] = []
    seen: set[str] = set()
    for prompt in resolved:
        key = str(Path(prompt)).lower()
        if key in seen:
            continue
        seen.add(key)
        deduped.append(prompt)
    return deduped


@click.group(name="story")
def story() -> None:
    """Add, list, and link user stories in the regression suite."""


@story.command("add")
@click.argument("source", required=False)
@click.option("--text", "inline_text", default=None, help="Inline issue/story text to use as the source.")
@click.option("--title", default=None, help="Human-readable story title used for duplicate checks.")
@click.option("--prompt", "prompts", multiple=True, help="Prompt path to link to the story.")
@click.option("--devunit", "devunits", multiple=True, help="Dev-unit name to resolve to a prompt file.")
@click.option("--stories-dir", default="user_stories", type=click.Path(file_okay=False))
@click.option("--prompts-dir", default=None, type=click.Path(file_okay=False))
@click.option("--dry-run", is_flag=True, help="Print what would be created without writing files.")
@click.option("--update", is_flag=True, help="Allow updating an existing story slug.")
@click.option("--generate-regression", is_flag=True, help="Print the pdd test --from-story handoff command.")
@click.option("--cross-devunit", is_flag=True, help="Document that multiple linked dev units are intentional.")
@click.option("--from-changed-files", is_flag=True, help="Use currently changed .prompt files from git status.")
def add_story(
    source: Optional[str],
    inline_text: Optional[str],
    title: Optional[str],
    prompts: tuple[str, ...],
    devunits: tuple[str, ...],
    stories_dir: str,
    prompts_dir: Optional[str],
    dry_run: bool,
    update: bool,
    generate_regression: bool,
    cross_devunit: bool,  # pylint: disable=unused-argument
    from_changed_files: bool,
) -> None:
    """Create a user story from an issue URL, file, or inline text."""
    if inline_text and source:
        raise click.ClickException("Use either SOURCE or --text, not both.")
    if not source and not inline_text:
        raise click.ClickException("Provide an issue URL/file/text source, or pass --text.")
    _validate_title_for_slug(title)
    changed_prompt_files = _changed_prompt_files(Path.cwd()) if from_changed_files else []
    prompt_files = _resolve_prompt_inputs(prompts, devunits)
    prompt_files.extend(changed_prompt_files)
    if not prompt_files:
        raise click.ClickException("Provide at least one --prompt, --devunit, or --from-changed-files.")

    story_root = Path(stories_dir)
    slug_seed = _story_slug_seed(title, inline_text)
    proposed_path = _proposed_story_path(slug_seed, story_root)
    if slug_seed and proposed_path.exists() and not update:
        raise click.ClickException(f"Story already exists: {proposed_path}. Use --update to overwrite.")

    if dry_run:
        click.echo(f"Dry run: would create {proposed_path}")
        click.echo("Linked prompts:")
        for prompt in prompt_files:
            click.echo(f"- {prompt}")
        if generate_regression:
            click.echo(
                "Issue #1700 handoff: after creating the story, run "
                "`pdd test --from-story <story-file> --output tests/story_regression/test_story_<slug>.py`."
            )
        return

    if slug_seed and proposed_path.exists() and update:
        success, message, _cost, _model, _linked_refs = cache_story_prompt_links(
            story_file=str(proposed_path),
            prompts_dir=prompts_dir,
            prompt_files=[Path(prompt) for prompt in prompt_files],
            force_relink=True,
        )
        if not success:
            raise click.ClickException(message)
        click.echo(message)
        if generate_regression:
            story_slug = story_id(proposed_path)
            click.echo(
                "Issue #1700 handoff: run "
                f"`pdd test --from-story {proposed_path} "
                f"--output tests/story_regression/test_story_{story_slug}.py`."
            )
        return

    issue_source = source or _inline_source_path(inline_text or "", title)
    success, message, _cost, _model, _story_path, _linked_refs = generate_user_story(
        prompt_files=prompt_files,
        issue=issue_source,
        output=str(proposed_path) if slug_seed else None,
        stories_dir=stories_dir,
        prompts_dir=prompts_dir,
        verbose=False,
    )
    if not success:
        raise click.ClickException(message)
    click.echo(message)
    if generate_regression:
        story_path = Path(_story_path)
        story_slug = story_id(story_path)
        click.echo(
            "Issue #1700 handoff: run "
            f"`pdd test --from-story {story_path} "
            f"--output tests/story_regression/test_story_{story_slug}.py`."
        )


story_cli = story


# Presence/freshness-honest labels for ``--with-regression-status``. This
# surface is static (no test execution), so it must never print "passing":
# pass/fail is verified separately by the story lane (``pytest -m story``).
_REGRESSION_STATUS_LABELS = {
    STATUS_MISSING: "missing",
    STATUS_STALE: "stale",
    STATUS_PASSING: "has-test",
}


def _project_tests_dir(story_path: Path) -> Path:
    """Resolve the *project's* tests dir from a story path (mirrors
    ``story_test_generation._default_output_for``): the ``tests/`` sibling of the
    directory that holds the story (its stories-dir), i.e. under the project root.

    Anchoring on the story's own parent dir (not ``Path.cwd()`` and not ``pdd``'s
    install dir) means pip-installed users -- and users passing a custom
    ``--stories-dir`` or running from a subdirectory -- scan their own suite, so
    linked tests are actually found. Falls back to ``cwd`` only for a story that
    has no parent directory at all (a bare filename).
    """
    stories_dir = story_path.parent
    root = stories_dir.parent if stories_dir != Path("") else Path.cwd()
    return root / "tests"


@story.command("list")
@click.option("--stories-dir", default="user_stories", type=click.Path(file_okay=False))
@click.option("--with-regression-status", is_flag=True)
def list_stories(stories_dir: str, with_regression_status: bool) -> None:
    """List known user stories and their linked prompts."""
    story_paths = discover_story_files(stories_dir)
    if not story_paths:
        click.echo("No user stories found.")
        return

    headers = ["Story", "Prompts"]
    if with_regression_status:
        headers.append("Regression")
    click.echo(" | ".join(headers))

    # Cache the collected story<->test map per resolved tests dir so a many-story
    # listing does not re-run pytest collection once per story.
    story_maps: dict[Path, object] = {}

    for story_path in story_paths:
        story_path = Path(story_path)
        try:
            story_text = story_path.read_text(encoding="utf-8")
        except OSError:
            story_text = ""
        prompt_refs = _parse_story_prompt_metadata(story_text)
        cells = [story_path.stem, ", ".join(prompt_refs) if prompt_refs else "-"]
        if with_regression_status:
            cells.append(_regression_status_label(story_path, story_maps))
        click.echo(" | ".join(cells))


def _regression_status_label(story_path: Path, story_maps: dict) -> str:
    """Presence/freshness-honest regression label (missing/has-test/stale).

    Reuses the gate's classification so hash-freshness is honored ("stale" is
    reachable) and never claims a test passed — the gate does not execute it.
    """
    tests_dir = _project_tests_dir(story_path)
    smap = story_maps.get(tests_dir)
    if smap is None:
        smap = build_story_map(tests_dir)
        story_maps[tests_dir] = smap
    try:
        evaluation = evaluate_story_regression(
            story_path, tests_dir=tests_dir, story_map=smap
        )
    except OSError:
        return _REGRESSION_STATUS_LABELS[STATUS_MISSING]
    return _REGRESSION_STATUS_LABELS.get(evaluation.status, evaluation.status)


@story.command("link")
@click.argument("story_file", type=click.Path(dir_okay=False))
@click.option("--prompt", "prompts", multiple=True, required=True, help="Prompt path to link.")
@click.option("--prompts-dir", default=None, type=click.Path(file_okay=False))
def link_story(story_file: str, prompts: tuple[str, ...], prompts_dir: Optional[str]) -> None:
    """Add or refresh pdd-story-prompts metadata on an existing story."""
    story_path = Path(story_file)
    if not story_path.is_file():
        raise click.ClickException(f"Story file not found: {story_file}")
    _validate_story_inside_user_stories(story_path)

    success, message, _cost, _model, _linked_refs = cache_story_prompt_links(
        story_file=str(story_path),
        prompts_dir=prompts_dir,
        prompt_files=[Path(prompt) for prompt in prompts],
        force_relink=True,
    )
    if not success:
        raise click.ClickException(message)
    click.echo(message)
