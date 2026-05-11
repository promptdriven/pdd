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
    Analyze a prompt and inject dependencies discovered in ``directory_path``.

    Returns a tuple of ``(modified_prompt, total_cost, model_name)``.
    """
    console = Console()
    quiet: bool = bool(ctx.obj.get("quiet", False)) if ctx.obj else False
    force: bool = bool(ctx.obj.get("force", False)) if ctx.obj else False

    try:
        # Lazy import: filelock is third-party
        try:
            from filelock import FileLock, Timeout  # type: ignore
        except ImportError:
            FileLock = None  # type: ignore
            Timeout = Exception  # type: ignore

        # Construct paths
        input_file_paths = {"prompt_file": prompt_file}
        command_options = {"output": output, "csv": auto_deps_csv_path}

        resolved_config, input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=force,
            quiet=quiet,
            command="auto-deps",
            command_options=command_options,
            context_override=ctx.obj.get("context") if ctx.obj else None,
            confirm_callback=ctx.obj.get("confirm_callback") if ctx.obj else None,
        )

        csv_path = output_file_paths.get("csv", "project_dependencies.csv")
        output_path = output_file_paths.get("output")

        # Acquire lock for the entire operation
        lock_path = f"{csv_path}.lock"
        lock_dir = Path(lock_path).parent
        try:
            lock_dir.mkdir(parents=True, exist_ok=True)
        except Exception:
            pass

        lock_ctx = FileLock(lock_path) if FileLock is not None else None

        def _run() -> Tuple[str, float, str]:
            # Force scan: remove existing CSV
            if force_scan and Path(csv_path).exists():
                if not quiet:
                    console.print(
                        f"[yellow]Removing existing CSV file due to --force-scan option: {csv_path}[/yellow]"
                    )
                try:
                    Path(csv_path).unlink()
                except Exception as e:
                    if not quiet:
                        console.print(f"[yellow]Warning: could not delete CSV file: {e}[/yellow]")

            # Resolve LLM params
            strength = ctx.obj.get("strength", DEFAULT_STRENGTH) if ctx.obj else DEFAULT_STRENGTH
            temperature = ctx.obj.get("temperature", 0) if ctx.obj else 0
            time_budget = ctx.obj.get("time", DEFAULT_TIME) if ctx.obj else DEFAULT_TIME
            verbose = not quiet

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

            # Save outputs
            if output_path:
                # Sanitize prompt output before writing
                cleaned_prompt, _removed = sanitize_prompt_output(modified_prompt, output_path)
                out_path_obj = Path(output_path)
                try:
                    out_path_obj.parent.mkdir(parents=True, exist_ok=True)
                except Exception:
                    pass
                out_path_obj.write_text(cleaned_prompt, encoding="utf-8")
                # Merge any newly inserted module includes into architecture.json
                # (best-effort; failures must not override successful auto-deps return).
                try:
                    from .auto_deps_architecture import (  # type: ignore
                        merge_auto_deps_includes_from_cwd,
                    )

                    merge_auto_deps_includes_from_cwd(
                        out_path_obj.resolve(),
                        input_strings.get("prompt_file", ""),
                        cleaned_prompt,
                    )
                except Exception:
                    pass
                modified_prompt = cleaned_prompt

            if csv_output:
                csv_path_obj = Path(csv_path)
                try:
                    csv_path_obj.parent.mkdir(parents=True, exist_ok=True)
                except Exception:
                    pass
                csv_path_obj.write_text(csv_output, encoding="utf-8")

            if not quiet:
                console.print(
                    "[bold green]Successfully analyzed and inserted dependencies![/bold green]"
                )
                console.print(f"[bold]Model used:[/bold] {model_name}")
                console.print(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
                if output_path:
                    console.print(f"[bold]Modified prompt saved to:[/bold] {output_path}")
                console.print(f"[bold]Dependency information saved to:[/bold] {csv_path}")

            # Fingerprint finalization (success path only)
            if output_path:
                try:
                    from .operation_log import save_fingerprint, infer_module_identity  # type: ignore

                    basename, language = infer_module_identity(prompt_file)
                    if basename and language:
                        paths = {"prompt": Path(output_path)}
                        save_fingerprint(
                            basename,
                            language,
                            operation="auto-deps",
                            paths=paths,
                            cost=total_cost,
                            model=model_name,
                        )
                except Exception:
                    pass
            else:
                if not quiet:
                    console.print(
                        "[yellow]Skipping fingerprint finalization: auto-deps did not write a modified prompt.[/yellow]"
                    )

            return modified_prompt, total_cost, model_name

        if lock_ctx is not None:
            with lock_ctx:
                return _run()
        else:
            return _run()

    except click.Abort:
        raise
    except Exception as exc:
        if not quiet:
            console.print(f"[red]Error in auto-deps: {exc}[/red]")
        return ("", 0.0, f"Error: {exc}")