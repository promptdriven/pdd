from __future__ import annotations

import sys
from pathlib import Path
from typing import Callable, Optional, Tuple

import click
from rich.console import Console

from . import DEFAULT_STRENGTH, DEFAULT_TIME
from .construct_paths import construct_paths
from .insert_includes import insert_includes
from .validate_prompt_includes import sanitize_prompt_output
from .operation_log import (
    infer_module_identity,
    save_fingerprint,
    clear_run_report,
)
from .auto_deps_architecture import merge_auto_deps_includes_from_cwd


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

    Analyzes a prompt file to discover and insert relevant dependencies
    (code examples and optionally documentation), with deduplication and
    parallelization support. Holds an exclusive file lock on the CSV path
    to prevent redundant LLM calls when multiple processes target the
    same cache.
    """
    console = Console()
    quiet = ctx.obj.get("quiet", False) if ctx.obj else False

    try:
        # Build path-construction inputs.
        input_file_paths = {"prompt_file": prompt_file}
        command_options = {
            "output": output,
            "csv": auto_deps_csv_path,
        }

        # Resolve paths via the shared path constructor.
        resolved = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj.get("force", False) if ctx.obj else False,
            quiet=quiet,
            command="auto-deps",
            command_options=command_options,
            context_override=ctx.obj.get("context") if ctx.obj else None,
            confirm_callback=ctx.obj.get("confirm_callback") if ctx.obj else None,
        )
        # construct_paths returns (resolved_config, input_strings, output_file_paths, language)
        _resolved_config, input_strings, output_file_paths, _ = resolved

        # Resolve CSV path with safe default.
        csv_path = output_file_paths.get("csv", "project_dependencies.csv")

        # Honor --force-scan by removing existing CSV so it gets rebuilt.
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
                        f"[yellow]Warning: failed to remove CSV file {csv_path}: {exc}[/yellow]"
                    )

        # Pull LLM parameters from the Click context with sensible defaults.
        strength = ctx.obj.get("strength", DEFAULT_STRENGTH) if ctx.obj else DEFAULT_STRENGTH
        temperature = ctx.obj.get("temperature", 0) if ctx.obj else 0
        time_budget = ctx.obj.get("time", DEFAULT_TIME) if ctx.obj else DEFAULT_TIME
        verbose = not quiet

        # Acquire an exclusive lock on the CSV path to serialize concurrent
        # auto-deps invocations targeting the same cache. The lock is held
        # for the entire operation so the CSV read/write cycle is atomic
        # from the caller's perspective.
        lock_path = Path(f"{csv_path}.lock")
        try:
            lock_path.parent.mkdir(parents=True, exist_ok=True)
        except OSError:
            # If we can't create the parent (unlikely if csv_path is valid),
            # fall through and let file open report a clear error.
            pass

        # Use function-scope import for the optional `filelock` dependency,
        # falling back to a no-op lock if it isn't installed.
        try:
            from filelock import FileLock  # type: ignore
            file_lock = FileLock(str(lock_path))
        except ImportError:
            class _NullLock:
                def __enter__(self):  # noqa: D401
                    return self

                def __exit__(self, exc_type, exc, tb):
                    return False

            file_lock = _NullLock()

        with file_lock:
            # Run the dependency insertion pipeline.
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

            # Sanitize the modified prompt before persisting so missing or
            # invalid `<include select=...>` tags don't survive to a later
            # `pdd sync` failure.
            output_path = output_file_paths["output"]
            cleaned_prompt, _warnings = sanitize_prompt_output(
                modified_prompt, output_path
            )

            # Write the cleaned modified prompt.
            output_path_obj = Path(output_path)
            output_path_obj.parent.mkdir(parents=True, exist_ok=True)
            output_path_obj.write_text(cleaned_prompt, encoding="utf-8")

            # Write the CSV cache only if non-empty.
            if csv_output:
                csv_path_obj = Path(csv_path)
                csv_path_obj.parent.mkdir(parents=True, exist_ok=True)
                csv_path_obj.write_text(csv_output, encoding="utf-8")

            # Merge any new <include> dependencies from the mutated prompt
            # into architecture.json. This helper has its own atomicity
            # guarantees and is intentionally outside the fingerprint
            # finalization block per the spec.
            try:
                merge_auto_deps_includes_from_cwd(
                    Path(output_path),
                    input_strings["prompt_file"],
                    cleaned_prompt,
                )
            except Exception as exc:  # noqa: BLE001
                if not quiet:
                    console.print(
                        f"[yellow]Warning: architecture.json merge skipped due to error: {exc}[/yellow]"
                    )

        # Console output (unless quiet).
        if not quiet:
            console.print(
                "[bold green]Successfully analyzed and inserted dependencies![/bold green]"
            )
            console.print(f"[bold]Model used:[/bold] {model_name}")
            console.print(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
            console.print(
                f"[bold]Modified prompt saved to:[/bold] {output_path}"
            )
            console.print(
                f"[bold]Dependency information saved to:[/bold] {csv_path}"
            )

        # Metadata finalization for the mutated prompt file. Errors here must
        # not mask the successful auto-deps result — log a warning and continue.
        #
        # Identity is derived from the *original* prompt file because the
        # default auto-deps output is `<basename>_<language>_with_deps.prompt`,
        # which would otherwise yield a bogus ``(<basename>_<language>_with,
        # deps)`` identity. The fingerprint records the hashes of the actual
        # mutated output file so subsequent sync runs can observe that the
        # canonical prompt diverges from the auto-deps result. This matches
        # the split contract: every successful ``pdd auto-deps`` writes a
        # fingerprint for the mutated prompt and clears any stale per-module
        # ``_run.json`` report.
        try:
            basename, language = infer_module_identity(Path(prompt_file))
            if basename is None or language is None:
                if not quiet:
                    console.print(
                        f"[yellow]Warning: could not infer module identity for "
                        f"{prompt_file}; skipping metadata finalization.[/yellow]"
                    )
            else:
                # Clear stale per-module run report because the prompt's
                # include-dependency surface changed.
                try:
                    clear_run_report(basename, language)
                except Exception as exc:  # noqa: BLE001
                    if not quiet:
                        console.print(
                            f"[yellow]Warning: failed to clear run report for "
                            f"{basename}/{language}: {exc}[/yellow]"
                        )

                # Persist the new fingerprint with current include-dependency
                # hashes computed from the mutated output file.
                try:
                    save_fingerprint(
                        basename=basename,
                        language=language,
                        operation="auto-deps",
                        paths={"prompt": Path(output_path)},
                        cost=total_cost,
                        model=model_name,
                    )
                except Exception as exc:  # noqa: BLE001
                    if not quiet:
                        console.print(
                            f"[yellow]Warning: failed to save fingerprint for "
                            f"{basename}/{language}: {exc}[/yellow]"
                        )
        except Exception as exc:  # noqa: BLE001
            if not quiet:
                console.print(
                    f"[yellow]Warning: metadata finalization skipped due to error: {exc}[/yellow]"
                )

        return cleaned_prompt, total_cost, model_name

    except click.Abort:
        # Re-raise so the orchestrator (e.g. sync loop) can stop cleanly.
        raise
    except Exception as exc:  # noqa: BLE001
        if not quiet:
            console.print(f"[bold red]Error in auto-deps: {exc}[/bold red]")
        return "", 0.0, f"Error: {exc}"