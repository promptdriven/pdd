from __future__ import annotations

from pathlib import Path
from typing import Callable, Optional, Tuple

import click
import filelock
from rich.console import Console

from . import DEFAULT_STRENGTH, DEFAULT_TIME
from .construct_paths import construct_paths
from .insert_includes import insert_includes
from .validate_prompt_includes import sanitize_prompt_output
from .auto_deps_architecture import merge_auto_deps_includes_from_cwd
from .operation_log import (
    infer_module_identity,
    save_fingerprint,
    clear_run_report,
    get_run_report_path,
)


def auto_deps_main(
    ctx: click.Context,
    prompt_file: str,
    directory_path: str,
    auto_deps_csv_path: Optional[str],
    output: Optional[str],
    force_scan: Optional[bool] = False,
    progress_callback: Optional[Callable[[int, int], None]] = None,
    include_docs: bool = False,
    no_dedup: bool = False,
    concurrency: int = 1,
) -> Tuple[str, float, str]:
    """
    CLI entry point for the `auto-deps` command.

    Analyzes the given prompt file, discovers dependencies (and optionally docs)
    in `directory_path`, inserts `<include>` directives, deduplicates redundant
    inline content (unless disabled), writes the modified prompt + dependency
    CSV, and finalizes per-module fingerprint metadata when overwriting the
    canonical prompt in place.

    Returns:
        (cleaned_prompt, total_cost, model_name) on success.
        ("", 0.0, f"Error: {exc}") on non-Abort failures so orchestrators can
        continue gracefully.
    """
    console = Console()
    quiet = ctx.obj.get("quiet", False) if ctx.obj else False

    try:
        # Build inputs for construct_paths
        input_file_paths = {"prompt_file": prompt_file}
        command_options = {"output": output, "csv": auto_deps_csv_path}

        force = ctx.obj.get("force", False) if ctx.obj else False
        context_override = ctx.obj.get("context") if ctx.obj else None
        confirm_callback = ctx.obj.get("confirm_callback") if ctx.obj else None

        resolved_config, input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=force,
            quiet=quiet,
            command="auto-deps",
            command_options=command_options,
            context_override=context_override,
            confirm_callback=confirm_callback,
        )

        # Resolve CSV path with default fallback
        csv_path = output_file_paths.get("csv", "project_dependencies.csv")

        # Acquire exclusive lock for the entire operation
        lock_path = Path(f"{csv_path}.lock")
        lock_path.parent.mkdir(parents=True, exist_ok=True)
        lock = filelock.FileLock(f"{csv_path}.lock")
        with lock:
            # Force-scan: delete existing CSV if requested
            if force_scan and Path(csv_path).exists():
                if not quiet:
                    console.print(
                        f"[yellow]Removing existing CSV file due to --force-scan option: {csv_path}[/yellow]"
                    )
                try:
                    Path(csv_path).unlink()
                except OSError as exc:
                    if not quiet:
                        console.print(
                            f"[yellow]Warning: Could not remove CSV file {csv_path}: {exc}[/yellow]"
                        )

            # LLM parameters
            strength = ctx.obj.get("strength", DEFAULT_STRENGTH) if ctx.obj else DEFAULT_STRENGTH
            temperature = ctx.obj.get("temperature", 0) if ctx.obj else 0
            time_budget = ctx.obj.get("time", DEFAULT_TIME) if ctx.obj else DEFAULT_TIME
            verbose = not quiet

            # Run insert_includes
            modified_prompt, csv_output, total_cost, model_name = insert_includes(
                input_prompt=input_strings["prompt_file"],
                directory_path=directory_path,
                csv_filename=csv_path,
                prompt_filename=prompt_file,
                strength=strength,
                temperature=temperature,
                time=time_budget,
                verbose=verbose,
                progress_callback=progress_callback,
                include_docs=include_docs,
                dedup=(not no_dedup),
                max_workers=concurrency,
            )

            # Sanitize prompt output before persisting (removes invalid <include>
            # selectors so a later `pdd sync` does not trip on them).
            output_path = output_file_paths["output"]
            cleaned_prompt, invalid_includes = sanitize_prompt_output(
                modified_prompt, output_path
            )
            if invalid_includes and not quiet:
                console.print(
                    f"[yellow]Warning: Cleaned {len(invalid_includes)} invalid "
                    f"<include> tag(s) before saving {output_path}: "
                    f"{invalid_includes}[/yellow]"
                )

            # Persist modified prompt
            Path(output_path).parent.mkdir(parents=True, exist_ok=True)
            with open(output_path, "w", encoding="utf-8") as fh:
                fh.write(cleaned_prompt)

            # Persist CSV if non-empty
            if csv_output:
                Path(csv_path).parent.mkdir(parents=True, exist_ok=True)
                with open(csv_path, "w", encoding="utf-8") as fh:
                    fh.write(csv_output)

            # Merge architecture.json dependencies (if architecture.json exists in project root)
            try:
                merge_result = merge_auto_deps_includes_from_cwd(
                    Path(output_path),
                    old_prompt_text=input_strings["prompt_file"],
                    new_prompt_text=cleaned_prompt,
                )
            except Exception as merge_exc:
                if not quiet:
                    console.print(
                        f"[yellow]Warning: architecture.json merge failed: {merge_exc}[/yellow]"
                    )
            else:
                # Non-exception failures (e.g. patcher returns updated=False with a
                # `messages` list) must still reach the user; otherwise the CLI
                # prints success while architecture.json was silently left unchanged.
                if isinstance(merge_result, dict) and not merge_result.get("updated", True):
                    if not quiet:
                        messages = merge_result.get("messages") or [
                            "merge_auto_deps_includes_from_cwd reported updated=False"
                        ]
                        for msg in messages:
                            console.print(
                                f"[yellow]Warning: architecture.json not updated: {msg}[/yellow]"
                            )

            # Console reporting
            if not quiet:
                console.print(
                    "[bold green]Successfully analyzed and inserted dependencies![/bold green]"
                )
                console.print(f"[bold]Model used:[/bold] {model_name}")
                console.print(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
                console.print(f"[bold]Modified prompt saved to:[/bold] {output_path}")
                console.print(f"[bold]Dependency information saved to:[/bold] {csv_path}")

            # Metadata finalization for every successful auto-deps mutation
            # (issue #989). Identity comes from the file that was actually
            # written (``output_path``); in in-place mode this resolves to the
            # canonical ``<basename>_<language>`` module, in the default CLI
            # flow it resolves to the ``<basename>_<language>_with_deps``
            # derivative. Errors are surfaced as warnings and never mask a
            # successful auto-deps result.
            try:
                basename, language = infer_module_identity(Path(output_path))
                if basename is None or language is None:
                    if not quiet:
                        console.print(
                            f"[yellow]Warning: Could not infer module identity for "
                            f"{output_path}; skipping fingerprint finalization.[/yellow]"
                        )
                else:
                    # Clear stale run report; do not let its failure block fingerprint save
                    try:
                        clear_run_report(basename, language)
                    except Exception as cr_exc:
                        if not quiet:
                            console.print(
                                f"[yellow]Warning: Failed to clear run report for "
                                f"{basename}_{language}: {cr_exc}[/yellow]"
                            )
                    # Defensive: clear_run_report() in pdd.operation_log silently swallows
                    # OSError on the actual unlink, so verify the report is really gone.
                    try:
                        _stale_report_path = get_run_report_path(basename, language)
                        if _stale_report_path.exists():
                            if not quiet:
                                console.print(
                                    f"[yellow]Warning: clear_run_report did not remove "
                                    f"{_stale_report_path}; downstream sync may still see "
                                    f"stale results.[/yellow]"
                                )
                    except Exception as _vrf_exc:
                        if not quiet:
                            console.print(
                                f"[yellow]Warning: could not verify run-report removal: "
                                f"{_vrf_exc}[/yellow]"
                            )
                    try:
                        save_fingerprint(
                            basename=basename,
                            language=language,
                            operation="auto-deps",
                            paths={"prompt": Path(output_path)},
                            cost=total_cost,
                            model=model_name,
                        )
                    except Exception as fp_exc:
                        if not quiet:
                            console.print(
                                f"[yellow]Warning: Failed to save fingerprint for "
                                f"{basename}_{language}: {fp_exc}[/yellow]"
                            )
            except Exception as meta_exc:
                # Never mask a successful auto-deps result on metadata errors
                if not quiet:
                    console.print(
                        f"[yellow]Warning: Metadata finalization encountered an error: {meta_exc}[/yellow]"
                    )

            return cleaned_prompt, total_cost, model_name

    except click.Abort:
        # Re-raise to allow orchestrators (e.g. pdd sync) to stop the loop
        raise
    except Exception as exc:
        if not quiet:
            console.print(f"[red]Error in auto-deps: {exc}[/red]")
        return "", 0.0, f"Error: {exc}"
