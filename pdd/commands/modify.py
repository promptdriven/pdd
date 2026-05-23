from __future__ import annotations

import click
from pathlib import Path
from rich.console import Console

from ..core.errors import handle_error
from ..track_cost import track_cost
from ..operation_log import log_operation

from ..split_main import split_main
from ..agentic_split import run_agentic_split
from ..change_main import change_main
from ..agentic_change import run_agentic_change
from ..update_main import update_main


console = Console()


@click.command("split")
@click.argument("args", nargs=-1)
@click.option("--legacy", is_flag=True, help="Use legacy split path.")
@click.option("--output-sub", help="Legacy: Optional path for saving the sub-prompt.")
@click.option("--output-modified", help="Legacy: Optional path for saving the modified prompt.")
@click.option("--diagnose", is_flag=True, help="Agentic: Run steps 0-2 only.")
@click.option("--propose-only", is_flag=True, help="Agentic: Run steps 0-4 only.")
@click.option("--delete-dead", is_flag=True, help="Agentic: Opt-in dead symbol deletion.")
@click.option("--force-split", is_flag=True, help="Agentic: Override LEAVE_ALONE diagnosis.")
@click.option("--no-verify", is_flag=True, help="Agentic: Skip test gate, dev only.")
@click.option("--skip-regen-gate", is_flag=True, help="Agentic: Skip regen, dev only, logged loudly.")
@click.option("--experimental-language", is_flag=True, help="Agentic: Opt-in for non-Python.")
@click.option("--no-github-state", is_flag=True, help="Agentic: Do not use github state.")
@click.option("--timeout-adder", type=float, default=0.0, help="Agentic: Extra timeout.")
@click.option("--intent", type=click.Choice(["reduce", "parallel", "reuse", "tests"]), help="Agentic: Skips step 0.")
@click.option("--no-phase-extraction", is_flag=True, help="Agentic: Skip phase helpers.")
@click.option("--strangler", is_flag=True, help="Agentic: Sequence N orchestrator passes.")
@click.option("--max-cost", type=click.FloatRange(min=0.01), default=None, help="Abort if total cost would cross USD threshold.")
@click.pass_context
@track_cost
def split(
    ctx: click.Context,
    args: tuple[str, ...],
    legacy: bool,
    output_sub: str | None,
    output_modified: str | None,
    diagnose: bool,
    propose_only: bool,
    delete_dead: bool,
    force_split: bool,
    no_verify: bool,
    skip_regen_gate: bool,
    experimental_language: bool,
    no_github_state: bool,
    timeout_adder: float,
    intent: str | None,
    no_phase_extraction: bool,
    strangler: bool,
    max_cost: float | None,
) -> tuple[str, float, str] | None:
    """Split large dev units into smaller, more manageable ones."""
    ctx.ensure_object(dict)

    try:
        if legacy:
            if len(args) != 3:
                raise click.UsageError("Legacy split requires exactly 3 arguments: input_prompt, input_code, example_code.")
            
            input_prompt, input_code, example_code = args
            for p in (input_prompt, input_code, example_code):
                if not Path(p).exists():
                    raise click.UsageError(f"Path does not exist: {p}")
            
            result_data, total_cost, model_name = split_main(
                ctx=ctx,
                input_prompt_file=input_prompt,
                input_code_file=input_code,
                example_code_file=example_code,
                output_sub=output_sub,
                output_modified=output_modified
            )
            return "Legacy split completed.", total_cost, model_name

        else:
            if len(args) != 1:
                raise click.UsageError("Agentic split requires exactly 1 argument: target_file.")
            
            target_file = args[0]
            ok, msg, cost, model, files = run_agentic_split(
                target_file=target_file,
                verbose=ctx.obj.get("verbose", False),
                quiet=ctx.obj.get("quiet", False),
                timeout_adder=timeout_adder,
                use_github_state=not no_github_state,
                diagnose_only=diagnose,
                propose_only=propose_only,
                delete_dead=delete_dead,
                force_split=force_split,
                no_verify=no_verify,
                skip_regen_gate=skip_regen_gate,
                experimental_language=experimental_language,
                intent=intent,
                no_phase_extraction=no_phase_extraction,
                strangler=strangler,
                max_cost=max_cost,
            )

            console.print(f"Status: {'Success' if ok else 'Failed'}")
            console.print(f"Message: {msg}")
            console.print(f"Cost: ${cost:.4f}")
            console.print(f"Model: {model}")
            if files:
                console.print("Changed files:")
                for f in files:
                    console.print(f"  - {f}")
            else:
                console.print("Changed files: (none)")

            if not ok:
                raise click.exceptions.Exit(1)
            
            return msg, cost, model
            
    except (click.Abort, click.UsageError, click.exceptions.Exit):
        raise
    except Exception as e:
        handle_error(e, "split", ctx.obj.get("quiet", False))
        return None


@click.command("change")
@click.argument("args", nargs=-1)
@click.option("--manual", is_flag=True, help="Run in manual mode.")
@click.option("--budget", type=float, default=5.0, help="Maximum budget in dollars.")
@click.option("--output", help="Output file path.")
@click.option("--csv", "use_csv", is_flag=True, help="Use CSV for batch processing in manual mode.")
@click.option("--timeout-adder", type=float, default=0.0, help="Extra timeout seconds.")
@click.option("--no-github-state", is_flag=True, help="Agentic: Do not use github state.")
@click.option("--clean-restart", is_flag=True, help="Discard any persisted solving state for this issue and start a fresh full pdd-issue flow from the default base branch, ignoring any previously generated change/issue-N branch artifacts. Use when recovering from a stopped or wrong-model run.")
@click.pass_context
@track_cost
def change(
    ctx: click.Context,
    args: tuple[str, ...],
    manual: bool,
    budget: float,
    output: str | None,
    use_csv: bool,
    timeout_adder: float,
    no_github_state: bool,
    clean_restart: bool,
) -> tuple[str, float, str] | None:
    """Modify an input prompt file based on a change prompt or issue."""
    ctx.ensure_object(dict)

    if clean_restart and manual:
        raise click.UsageError("--clean-restart is only valid in agentic mode and cannot be used with --manual")

    try:
        if manual:
            if use_csv:
                if len(args) != 2:
                    raise click.UsageError("CSV mode requires exactly 2 arguments: change_file and input_code_directory.")
                change_file, input_code = args
                if not Path(change_file).exists():
                    raise click.UsageError(f"File not found: {change_file}")
                if not Path(input_code).exists():
                    raise click.UsageError(f"Path not found: {input_code}")
                if not Path(input_code).is_dir():
                    raise click.UsageError(f"input_code must be a directory in CSV mode: {input_code}")
                input_prompt = None
            else:
                if len(args) != 3:
                    raise click.UsageError("Manual mode requires exactly 3 arguments: change_file, input_code_file, input_prompt_file.")
                change_file, input_code, input_prompt = args
                for p in (change_file, input_code, input_prompt):
                    if not Path(p).exists():
                        raise click.UsageError(f"File not found: {p}")
                if Path(input_code).is_dir():
                    raise click.UsageError(f"input_code must be a file in standard manual mode (not a directory): {input_code}")
            
            ctx.obj["budget"] = budget
            msg, cost, model = change_main(
                ctx=ctx,
                change_prompt_file=change_file,
                input_code=input_code,
                input_prompt_file=input_prompt,
                output=output,
                use_csv=use_csv,
                budget=budget,
            )
            return msg, cost, model

        else:
            if len(args) != 1:
                raise click.UsageError("Agentic mode requires exactly 1 argument: issue_url.")
            issue_url = args[0]
            ok, msg, cost, model, files = run_agentic_change(
                issue_url=issue_url,
                verbose=ctx.obj.get("verbose", False),
                quiet=ctx.obj.get("quiet", False),
                timeout_adder=timeout_adder,
                use_github_state=not no_github_state,
                clean_restart=clean_restart,
            )

            console.print(f"Status: {'Success' if ok else 'Failed'}")
            console.print(f"Message: {msg}")
            console.print(f"Cost: ${cost:.4f}")
            console.print(f"Model: {model}")
            if files:
                console.print("Changed files:")
                for f in files:
                    console.print(f"  - {f}")
            else:
                console.print("Changed files: (none)")

            if not ok:
                raise click.exceptions.Exit(1)

            return msg, cost, model

    except (click.Abort, click.UsageError, click.exceptions.Exit):
        raise
    except Exception as e:
        handle_error(e, "change", ctx.obj.get("quiet", False))
        return None


@click.command("update")
@click.argument("files", nargs=-1)
@click.option("--all", "all_", is_flag=True, help="Update all changed pairs in repo.")
@click.option("--extensions", help="Comma separated list of extensions.")
@click.option("--directory", help="Target directory for repo update.")
@click.option("--git", "use_git", is_flag=True, help="Use git diff to inform updates.")
@click.option("--output", help="Output file path.")
@click.option("--simple", is_flag=True, help="Use simple output formatting.")
@click.option("--base-branch", default="main", help="Base branch for git diff.")
@click.option("--budget", type=float, default=None, help="Maximum cost budget.")
@click.option("--dry-run", is_flag=True, help="Dry run mode.")
@click.option("--sync-metadata", is_flag=True, default=False, help="After update, run the shared metadata-sync orchestrator (preserve/seed PDD tags, reconcile architecture.json entry, clear stale run reports, finalize fingerprint last). On any stage failed, exits non-zero. Stages may report skipped for legitimate cases (no architecture.json, unregistered modules). LLM-first refresh of stale-but-present tags is tracked at #870 and is NOT invoked here.")
@click.pass_context
@log_operation(operation="update", clears_run_report=True)
@track_cost
def update(
    ctx: click.Context,
    files: tuple[str, ...],
    all_: bool,
    extensions: str | None,
    directory: str | None,
    use_git: bool,
    output: str | None,
    simple: bool,
    base_branch: str,
    budget: float | None,
    dry_run: bool,
    sync_metadata: bool,
) -> tuple[str, float, str] | None:
    """Update the original prompt file based on code changes."""
    ctx.ensure_object(dict)

    if budget is not None and budget <= 0:
        raise click.UsageError("--budget must be > 0.")
    if len(files) > 3:
        raise click.UsageError("update takes at most 3 file arguments.")
    if len(files) == 2 and not use_git:
        raise click.UsageError("2 arguments requires --git.")
    if len(files) == 3 and use_git:
        raise click.UsageError("3 arguments forbids --git.")
    if all_ and files:
        raise click.UsageError("--all forbidden with file paths.")

    repo = len(files) == 0 or all_
    
    if repo:
        if use_git or output:
            raise click.UsageError("Repo mode (0 args or --all) forbids --git and --output.")
    else:
        if extensions or directory or base_branch != "main" or dry_run or budget is not None:
            raise click.UsageError("File modes forbid --extensions, --directory, non-default --base-branch, --dry-run, and --budget.")

    input_prompt_file = None
    modified_code_file = None
    input_code_file = None

    if len(files) == 1:
        modified_code_file = files[0]
    elif len(files) == 2:
        input_prompt_file = files[0]
        modified_code_file = files[1]
    elif len(files) == 3:
        input_prompt_file = files[0]
        modified_code_file = files[1]
        input_code_file = files[2]

    try:
        result = update_main(
            ctx=ctx,
            input_prompt_file=input_prompt_file,
            modified_code_file=modified_code_file,
            input_code_file=input_code_file,
            output=output,
            use_git=use_git,
            repo=repo,
            extensions=extensions,
            directory=directory,
            simple=simple,
            base_branch=base_branch,
            budget=budget,
            dry_run=dry_run,
            sync_metadata=sync_metadata
        )
        return result
    except (click.Abort, click.UsageError, click.exceptions.Exit):
        raise
    except Exception as e:
        handle_error(e, "update", ctx.obj.get("quiet", False))
        return None