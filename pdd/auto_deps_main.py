from __future__ import annotations

from contextlib import nullcontext
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
    clear_run_report,
    infer_module_identity,
    resolve_fingerprint_paths,
    save_fingerprint,
    get_run_report_path,
    get_fingerprint_path,
)
from .fingerprint_transaction import AtomicStateUpdate, FingerprintFinalizeError


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
    compress: bool = False,
    _skip_finalization: bool = False,
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
    from .sync_core.finalize import preflight_legacy_mutation
    preflight_legacy_mutation({"prompt": Path(prompt_file)})
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
        output_path = Path(output_file_paths["output"])
        unit_basename, unit_language = infer_module_identity(output_path)
        outer_state = None
        if unit_basename and unit_language:
            outer_state = AtomicStateUpdate(
                unit_basename,
                unit_language,
                directory=get_fingerprint_path(
                    unit_basename, unit_language, paths={"prompt": output_path}
                ).parent,
            )

        # Acquire exclusive lock for the entire operation
        lock_path = Path(f"{csv_path}.lock")
        lock_path.parent.mkdir(parents=True, exist_ok=True)
        lock = filelock.FileLock(f"{csv_path}.lock")
        with outer_state if outer_state is not None else nullcontext(), lock:
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
                compress=compress,
            )

            # Sanitize prompt output before persisting (removes invalid <include>
            # selectors so a later `pdd sync` does not trip on them).
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
                # Non-exception failures must still reach the user; otherwise the
                # CLI prints success while architecture.json was silently left
                # unchanged. ``updated=False`` is also returned for legitimate
                # no-ops (auto_deps_architecture.py:326 — nothing needed adding),
                # so gate the warning on ``added_dependencies`` being non-empty:
                # that distinguishes "we wanted to write X but couldn't" from
                # "nothing to write."
                if (
                    isinstance(merge_result, dict)
                    and not merge_result.get("updated", True)
                    and merge_result.get("added_dependencies")
                ):
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
            #
            # ``_skip_finalization=True`` is set by ``pdd sync`` because it
            # invokes auto-deps with a temp ``<basename>_<language>_with_deps``
            # output that it then ``shutil.move``s onto the canonical prompt;
            # writing a fingerprint for that temp identity here would leave
            # ``.pdd/meta/*_with_deps.json`` orphaned after the move, and the
            # derivative's identity is the wrong target for run-report clears
            # (sync owns the canonical fingerprint write and the canonical
            # run-report clear on its side).
            if _skip_finalization:
                return cleaned_prompt, total_cost, model_name
            try:
                basename, language = unit_basename, unit_language
                if basename is None or language is None:
                    # Outputs outside PDD's managed prompt naming scheme have
                    # no canonical unit identity and therefore no fingerprint.
                    return cleaned_prompt, total_cost, model_name
                else:
                    # Issue #1211: route clear/verify/save through the same
                    # `paths` hint (the prompt path we just wrote) so all
                    # three target the subproject's .pdd/meta — not a parent
                    # CWD orphan — when auto-deps is run from above the
                    # subproject root.
                    _autodeps_paths = resolve_fingerprint_paths(
                        basename, language, Path(output_path), paths={"prompt": Path(output_path)}
                    )
                    save_fingerprint(
                        basename=basename, language=language, operation="auto-deps",
                        paths=_autodeps_paths, cost=total_cost, model=model_name,
                        remove_run_report=True,
                    )
            except FingerprintFinalizeError:
                raise

            return cleaned_prompt, total_cost, model_name

    except click.Abort:
        # Re-raise to allow orchestrators (e.g. pdd sync) to stop the loop
        raise
    except Exception as exc:
        from .sync_core.finalize import CanonicalFinalizationError
        if isinstance(exc, (CanonicalFinalizationError, FingerprintFinalizeError)):
            raise
        if not quiet:
            console.print(f"[red]Error in auto-deps: {exc}[/red]")
        return "", 0.0, f"Error: {exc}"
