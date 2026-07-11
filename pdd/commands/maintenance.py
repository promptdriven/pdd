"""
Maintenance commands (sync, auto_deps, setup).
"""
import os
import click
from typing import Any, Dict, Mapping, Optional, Tuple
from pathlib import Path

from ..architecture_sync import sync_prompts_to_architecture
from ..sync_main import sync_main
from ..auto_deps_main import auto_deps_main
from ..agentic_sync import _is_github_issue_url, run_agentic_sync, run_global_sync
from ..construct_paths import _find_pddrc_file, _load_pddrc_config
from ..track_cost import track_cost
from ..core.errors import handle_error
from ..sync_determine_operation import AmbiguousModuleError
from ..fingerprint_transaction import FingerprintFinalizeError
from ..core.utils import _run_setup_utility, echo_model_line
from ..evidence_manifest import (
    collect_sync_evidence_paths,
    grounding_kwargs_from_ctx,
    validation_from_sync,
    write_evidence_manifest,
)

DEFAULT_SYNC_BUDGET = 20.0


def _write_sync_evidence_manifest(
    *,
    basename: str,
    result: Mapping[str, Any],
    total_cost: float,
    model_name: str,
    skip_tests: bool,
    skip_verify: bool,
    dry_run: bool,
    temperature: float,
    quiet: bool,
    context_snapshot: Optional[Mapping[str, Any]] = None,
    grounding: Optional[Mapping[str, Any]] = None,
    reviewed: bool = False,
    compression: Optional[Mapping[str, Any]] = None,
    agentic_fallback: Optional[Mapping[str, Any]] = None,
    compress: bool = False,
) -> None:
    """Write or refresh the dev-unit evidence manifest for a sync attempt."""
    project_root = Path.cwd()
    prompt_path, output_files = collect_sync_evidence_paths(
        basename,
        result,
        project_root=project_root,
    )
    manifest_path = write_evidence_manifest(
        command="pdd sync",
        basename=basename,
        prompt_file=prompt_path,
        output_files=output_files,
        model=model_name,
        cost_usd=total_cost,
        temperature=temperature,
        compress=compress,
        validation=validation_from_sync(
            result,
            skip_tests=skip_tests,
            skip_verify=skip_verify,
            dry_run=dry_run,
        ),
        project_root=project_root,
        context_snapshot=context_snapshot,
        grounding=grounding,
        reviewed=reviewed,
        compression=compression,
        agentic_fallback=agentic_fallback,
    )
    if not quiet:
        click.echo(
            click.style(
                f"Evidence manifest: {manifest_path}",
                fg="cyan",
            )
        )


@click.command("sync")
@click.argument("basename", required=False)
@click.option(
    "--max-attempts",
    type=int,
    default=None,
    help="Maximum number of fix attempts. Default: 3 or .pddrc value.",
)
@click.option(
    "--budget",
    type=float,
    default=None,
    help="Maximum total cost for the sync process. Default: 20.0 or .pddrc value.",
)
@click.option(
    "--skip-verify",
    is_flag=True,
    default=False,
    help="Skip the functional verification step.",
)
@click.option(
    "--skip-tests",
    is_flag=True,
    default=False,
    help="Skip unit test generation and fixing.",
)
@click.option(
    "--target-coverage",
    type=float,
    default=None,
    help="Desired code coverage percentage. Default: 90.0 or .pddrc value.",
)
@click.option(
    "--dry-run",
    is_flag=True,
    default=False,
    help="Analyze sync state without executing operations. Shows what sync would do.",
)
@click.option("--json", "as_json", is_flag=True, default=False, help="Emit machine-readable dry-run JSON.")
@click.option(
    "--log",
    is_flag=True,
    default=False,
    hidden=True,
    help="Deprecated: Use --dry-run instead.",
)
@click.option(
    "--no-steer",
    "no_steer",
    is_flag=True,
    default=False,
    help="Disable interactive steering of sync operations.",
)
@click.option(
    "--steer-timeout",
    type=float,
    default=None,
    help="Timeout in seconds for steering prompts (default: 8.0).",
)
@click.option(
    "--agentic",
    is_flag=True,
    default=False,
    help="Use agentic mode for Python (skip iterative loops, trust agent results).",
)
@click.option(
    "--timeout-adder",
    type=float,
    default=0.0,
    help="Additional seconds added on top of the per-module wall-clock cap "
    "(stacks with PDD_MODULE_TIMEOUT_SECONDS, default 2700s; agentic sync mode).",
)
@click.option(
    "--no-github-state",
    is_flag=True,
    default=False,
    help="Disable GitHub comment updates (agentic sync mode).",
)
@click.option(
    "--one-session/--no-one-session",
    default=None,
    help="Run example/crash/verify/test/fix in a single agentic session. Default: enabled for agentic sync (issue URL), disabled for single-module sync.",
)
@click.option(
    "--durable",
    is_flag=True,
    default=False,
    help="Use isolated worktrees and checkpoint commits for GitHub issue sync.",
)
@click.option(
    "--durable-branch",
    default=None,
    help="Branch to use for durable checkpoint commits. Default: sync/issue-<N>.",
)
@click.option(
    "--no-resume",
    is_flag=True,
    default=False,
    help="In durable mode, ignore existing checkpoint trailers and rerun modules.",
)
@click.option(
    "--durable-max-parallel",
    type=int,
    default=None,
    help="Maximum parallel module worktrees in durable mode. Default: current runner concurrency.",
)
@click.option(
    "--evidence",
    is_flag=True,
    default=False,
    help="Write a machine-readable evidence manifest for this run.",
)
@click.option(
    "--snapshot-context",
    is_flag=True,
    default=False,
    help=(
        "Write replayable expanded prompt context artifacts (single-module sync "
        "only). Replay via pdd replay on .pdd/evidence/runs/<run_id>.json."
    ),
)
@click.option(
    "--compress",
    is_flag=True,
    default=False,
    help=(
        "Use AST-based compression for Python few-shot includes during sync "
        "(auto-deps tags and generate preprocess expansion)."
    ),
)
@click.option(
    "--compressed-context/--no-compressed-context",
    default=None,
    help=(
        "Enable bounded compressed sync context. Omit to use .pddrc "
        "defaults.compressed_context, falling back to disabled."
    ),
)
@click.option(
    "--model",
    "model",
    default=None,
    help="Override the base model for this sync run (sets PDD_MODEL_DEFAULT "
         "for the invocation, e.g. --model chatgpt/gpt-5.3-codex). Applies to "
         "the local llm_invoke route; for a chatgpt/* subscription model on a "
         "cloud-enabled install, also pass --local. Takes precedence over the "
         "PDD_MODEL_DEFAULT env var for this run only.",
)
@click.option(
    "--compress-examples",
    is_flag=True,
    default=None,
    help="Automatically apply mode=\"interface\" to example includes.",
)
@click.option(
    "--compress-test-context",
    is_flag=True,
    default=None,
    help="Automatically compress test context to failing tests only.",
)
@click.option(
    "--context-compression",
    type=click.Choice(["off", "test", "examples", "contracts", "all"]),
    default=None,
    help="Set context compression mode for this sync run.",
)
@click.option(
    "--compression-fallback",
    type=click.Choice(["full", "error"]),
    default=None,
    help="Behavior when context compression fails (default: full).",
)
@click.pass_context
@track_cost
def sync(
    ctx: click.Context,
    basename: Optional[str],
    max_attempts: Optional[int],
    budget: Optional[float],
    skip_verify: bool,
    skip_tests: bool,
    target_coverage: Optional[float],
    dry_run: bool,
    as_json: bool,
    log: bool,
    no_steer: bool,
    steer_timeout: Optional[float],
    agentic: bool,
    timeout_adder: float,
    no_github_state: bool,
    one_session: Optional[bool],
    durable: bool,
    durable_branch: Optional[str],
    no_resume: bool,
    durable_max_parallel: Optional[int],
    evidence: bool,
    snapshot_context: bool,
    compress: bool,
    compressed_context: Optional[bool],
    model: Optional[str] = None,
    compress_examples: Optional[bool] = None,
    compress_test_context: Optional[bool] = None,
    context_compression: Optional[str] = None,
    compression_fallback: Optional[str] = None,
) -> Optional[Tuple[str, float, str]]:
    """
    Synchronize prompts with code and tests.

    BASENAME is the base name of the prompt file (e.g., 'my_module' for
    'prompts/my_module_python.prompt'), a GitHub issue URL for agentic
    multi-module sync, or omitted for project-wide Tier 1 architecture sync.
    """
    from ..config_resolution import merge_cli_compression_override

    ctx.ensure_object(dict)
    cli_compression: dict[str, object] = {}
    if compress_examples is not None:
        ctx.obj["compress_examples"] = compress_examples
        cli_compression["compress_examples"] = compress_examples
    if compress_test_context is not None:
        ctx.obj["compress_test_context"] = compress_test_context
        cli_compression["compress_test_context"] = compress_test_context
    if context_compression is not None:
        ctx.obj["context_compression"] = context_compression
        cli_compression["context_compression"] = context_compression
    if compression_fallback is not None:
        ctx.obj["compression_fallback"] = compression_fallback
        cli_compression["compression_fallback"] = compression_fallback
    if cli_compression:
        merge_cli_compression_override(cli_compression)

    # Honor an explicit per-run model override (CLI > env, issue #1269).
    # Set PDD_MODEL_DEFAULT: subprocess/agentic sync paths inherit the env and
    # read it at their own import, and the in-process llm_invoke path resolves
    # the base model from this env var at CALL time. NOTE: this steers the LOCAL
    # llm_invoke route only — the cloud route serializes no model override or
    # Codex auth, so a chatgpt/* subscription model on a cloud-enabled install
    # also needs --local (PDD_FORCE_LOCAL=1). See the --model help / README.
    if model:
        # Scope the override to THIS invocation: restore the prior value when
        # the command's Click context closes, so a long-lived in-process caller
        # (CliRunner, embedding) does not leak the model into later runs (#1269).
        _prev_model_default = os.environ.get("PDD_MODEL_DEFAULT")
        os.environ["PDD_MODEL_DEFAULT"] = model

        def _restore_model_default(_prev=_prev_model_default):
            if _prev is None:
                os.environ.pop("PDD_MODEL_DEFAULT", None)
            else:
                os.environ["PDD_MODEL_DEFAULT"] = _prev

        ctx.call_on_close(_restore_model_default)
    # Handle deprecated --log flag
    if log:
        click.echo(
            click.style(
                "Warning: --log is deprecated, use --dry-run instead.",
                fg="yellow"
            ),
            err=True
        )
        dry_run = True

    if as_json:
        if not dry_run:
            raise click.UsageError("--json is only supported with sync --dry-run.")
        if basename and _is_github_issue_url(basename):
            raise click.UsageError("--json dry-run is not supported for GitHub issue sync.")
        from ..continuous_sync import build_report
        import json as _json

        ctx.obj["_suppress_result_summary"] = True
        report = build_report(
            consumer="sync-dry-run",
            modules=[basename] if basename else None,
        )
        click.echo(_json.dumps(report, indent=2, sort_keys=True))
        return None

    effective_compressed_context = _resolve_compressed_context(compressed_context)
    ctx.obj["compressed_context"] = effective_compressed_context

    # No basename -> global Tier 1 sync
    if basename is None:
        if snapshot_context:
            raise click.UsageError("--snapshot-context is only supported for single-module sync.")
        if durable or durable_branch or no_resume or durable_max_parallel is not None:
            raise click.UsageError("Durable sync options require a GitHub issue URL.")
        effective_one_session = one_session if one_session is not None else False
        global_result = _run_global_sync_dispatch(
            ctx=ctx,
            budget=budget,
            skip_verify=skip_verify,
            skip_tests=skip_tests,
            target_coverage=target_coverage,
            dry_run=dry_run,
            agentic=agentic,
            no_steer=no_steer,
            max_attempts=max_attempts,
            one_session=effective_one_session,
            timeout_adder=timeout_adder,
            compressed_context=effective_compressed_context,
        )
        if evidence and global_result:
            _, cost, model = global_result
            write_evidence_manifest(
                command="pdd sync",
                model=model,
                cost_usd=cost,
                temperature=ctx.obj.get("temperature", 0.0),
                basename="global-sync",
                validation={
                    "detect_stories": "not_available",
                    "unit_tests": "not_available",
                    "verify": "not_available",
                },
                compression={
                    "enabled": effective_compressed_context,
                    "requested": effective_compressed_context,
                    "used": False,
                    "mode": "compressed-sync-context",
                    "phases": [],
                },
            )
        return global_result

    # Detect GitHub issue URL -> dispatch to agentic sync
    if _is_github_issue_url(basename):
        if snapshot_context:
            raise click.UsageError("--snapshot-context is only supported for single-module sync.")
        if not durable and (
            durable_branch is not None or no_resume or durable_max_parallel is not None
        ):
            raise click.UsageError(
                "--durable-branch, --no-resume, and --durable-max-parallel require --durable."
            )
        # Default to one-session for agentic sync unless explicitly disabled
        effective_one_session = one_session if one_session is not None else True
        agentic_result = _run_agentic_sync_dispatch(
            ctx=ctx,
            issue_url=basename,
            budget=budget,
            skip_verify=skip_verify,
            skip_tests=skip_tests,
            dry_run=dry_run,
            agentic=agentic,
            no_steer=no_steer,
            max_attempts=max_attempts,
            timeout_adder=timeout_adder,
            no_github_state=no_github_state,
            one_session=effective_one_session,
            durable=durable,
            durable_branch=durable_branch,
            no_resume=no_resume,
            durable_max_parallel=durable_max_parallel,
            strength=ctx.obj.get("strength"),
            temperature=ctx.obj.get("temperature"),
            context_override=ctx.obj.get("context"),
            compressed_context=effective_compressed_context,
        )
        if evidence and agentic_result:
            _, cost, model = agentic_result
            write_evidence_manifest(
                command="pdd sync",
                model=model,
                cost_usd=cost,
                temperature=ctx.obj.get("temperature", 0.0),
                basename="agentic-sync",
                validation={
                    "detect_stories": "not_available",
                    "unit_tests": "not_available",
                    "verify": "not_available",
                },
                compression={
                    "enabled": effective_compressed_context,
                    "requested": effective_compressed_context,
                    "used": False,
                    "mode": "compressed-sync-context",
                    "phases": [],
                },
                agentic_fallback={
                    "attempted": True,
                    "used": True,
                    "phases": ["agentic-sync"],
                    "reason": "GitHub issue sync uses agentic module selection and child sync dispatch",
                },
            )
        return agentic_result

    if durable or durable_branch or no_resume or durable_max_parallel is not None:
        raise click.UsageError("Durable sync options require a GitHub issue URL.")

    try:
        # Default to multi-step for single-module sync unless explicitly enabled
        effective_one_session = one_session if one_session is not None else False
        result, total_cost, model_name = sync_main(
            ctx=ctx,
            basename=basename,
            max_attempts=max_attempts,
            budget=budget,
            skip_verify=skip_verify,
            skip_tests=skip_tests,
            target_coverage=target_coverage,
            dry_run=dry_run,
            no_steer=no_steer,
            steer_timeout=steer_timeout,
            agentic_mode=agentic,
            one_session=effective_one_session,
            snapshot_context=snapshot_context,
            compress=compress,
            compressed_context=effective_compressed_context,
        )
        if evidence:
            _write_sync_evidence_manifest(
                basename=basename,
                result=result,
                total_cost=total_cost,
                model_name=model_name,
                skip_tests=skip_tests,
                skip_verify=skip_verify,
                dry_run=dry_run,
                temperature=ctx.obj.get("temperature", 0.0),
                quiet=ctx.obj.get("quiet", False),
                context_snapshot=(ctx.obj or {}).get("context_snapshot"),
                compress=compress,
                compression=_compression_from_sync_result(result),
                agentic_fallback=_agentic_fallback_from_sync_result(result),
                **grounding_kwargs_from_ctx(ctx.obj),
            )
        return str(result), total_cost, model_name
    except click.Abort:
        raise
    except AmbiguousModuleError as exc:
        # Issue #1677: an ambiguous module name is a hard, actionable error. Always
        # print the choices (even under --quiet) and exit non-zero, so CI/automation,
        # quiet runs and the agentic child runners never read it as success.
        handle_error(exc, "sync", quiet=False)
        raise click.exceptions.Exit(1)
    except Exception as exception:
        if evidence and basename and not _is_github_issue_url(basename):
            _write_sync_evidence_manifest(
                basename=basename,
                result={"overall_success": False, "results_by_language": {}},
                total_cost=0.0,
                model_name="",
                skip_tests=skip_tests,
                skip_verify=skip_verify,
                dry_run=dry_run,
                temperature=ctx.obj.get("temperature", 0.0),
                quiet=ctx.obj.get("quiet", False),
            )
        handle_error(exception, "sync", ctx.obj.get("quiet", False))
        return None


def _run_agentic_sync_dispatch(
    ctx: click.Context,
    issue_url: str,
    budget: Optional[float],
    skip_verify: bool,
    skip_tests: bool,
    dry_run: bool,
    agentic: bool,
    no_steer: bool,
    max_attempts: Optional[int],
    timeout_adder: float,
    no_github_state: bool,
    one_session: bool = False,
    durable: bool = False,
    durable_branch: Optional[str] = None,
    no_resume: bool = False,
    durable_max_parallel: Optional[int] = None,
    strength: Optional[float] = None,
    temperature: Optional[float] = None,
    context_override: Optional[str] = None,
    compressed_context: bool = False,
) -> Optional[Tuple[str, float, str]]:
    """Dispatch to agentic sync runner for GitHub issue URLs."""
    ctx.ensure_object(dict)
    quiet = ctx.obj.get("quiet", False)
    verbose = ctx.obj.get("verbose", False)

    try:
        success, message, cost, model = run_agentic_sync(
            issue_url=issue_url,
            verbose=verbose,
            quiet=quiet,
            budget=budget,
            skip_verify=skip_verify,
            skip_tests=skip_tests,
            dry_run=dry_run,
            agentic_mode=agentic,
            no_steer=no_steer,
            max_attempts=max_attempts,
            timeout_adder=timeout_adder,
            use_github_state=not no_github_state,
            one_session=one_session,
            reasoning_time=ctx.obj.get("time") if ctx.obj.get("time_explicit") else None,
            durable=durable,
            durable_branch=durable_branch,
            no_resume=no_resume,
            durable_max_parallel=durable_max_parallel,
            strength=strength,
            temperature=temperature,
            context_override=context_override,
            compressed_context=compressed_context,
            local=ctx.obj.get("local", False),
        )

        if not quiet:
            status = "Success" if success else "Failed"
            click.echo(f"Status: {status}")
            click.echo(f"Message: {message}")
            click.echo(f"Cost: ${cost:.4f}")
            echo_model_line(model)

        if not success:
            raise click.exceptions.Exit(1)

        return message, cost, model

    except (click.Abort, click.exceptions.Exit):
        raise
    except AmbiguousModuleError as exc:
        # Issue #1677: fail hard on an ambiguous module name (see the single-module
        # sync handler) — always print and exit non-zero so automation never treats it
        # as success.
        handle_error(exc, "sync", quiet=False)
        raise click.exceptions.Exit(1)
    except Exception as exception:
        handle_error(exception, "sync", ctx.obj.get("quiet", False))
        return None


def _run_global_sync_dispatch(
    ctx: click.Context,
    budget: Optional[float],
    skip_verify: bool,
    skip_tests: bool,
    target_coverage: Optional[float],
    dry_run: bool,
    agentic: bool,
    no_steer: bool,
    max_attempts: Optional[int],
    one_session: bool = False,
    timeout_adder: float = 0.0,
    compressed_context: bool = False,
) -> Optional[Tuple[str, float, str]]:
    """Dispatch to global sync runner for no-argument `pdd sync`."""
    ctx.ensure_object(dict)
    quiet = ctx.obj.get("quiet", False)
    verbose = ctx.obj.get("verbose", False)
    effective_budget = _resolve_global_sync_budget(budget)
    effective_target_coverage = _resolve_global_sync_target_coverage(target_coverage)

    try:
        success, message, cost, model = run_global_sync(
            verbose=verbose,
            quiet=quiet,
            budget=effective_budget,
            skip_verify=skip_verify,
            skip_tests=skip_tests,
            agentic_mode=agentic,
            no_steer=no_steer,
            max_attempts=max_attempts,
            dry_run=dry_run,
            target_coverage=effective_target_coverage,
            one_session=one_session,
            local=ctx.obj.get("local", False),
            timeout_adder=timeout_adder,
            strength=ctx.obj.get("strength"),
            temperature=ctx.obj.get("temperature"),
            context_override=ctx.obj.get("context"),
            compressed_context=compressed_context,
        )

        if not quiet:
            status = "Success" if success else "Failed"
            click.echo(f"Status: {status}")
            click.echo(f"Message: {message}")
            click.echo(f"Cost: ${cost:.4f}")
            echo_model_line(model)

        if not success:
            raise click.exceptions.Exit(1)

        return message, cost, model

    except (click.Abort, click.exceptions.Exit):
        raise
    except AmbiguousModuleError as exc:
        # Issue #1677: fail hard on an ambiguous module name (see the single-module
        # sync handler) — always print and exit non-zero so automation never treats it
        # as success.
        handle_error(exc, "sync", quiet=False)
        raise click.exceptions.Exit(1)
    except Exception as exception:
        handle_error(exception, "sync", ctx.obj.get("quiet", False))
        return None


def _resolve_global_sync_budget(budget: Optional[float]) -> float:
    """Resolve no-argument global sync budget from CLI, .pddrc, or default."""
    if budget is not None:
        return budget

    pddrc_path = _find_pddrc_file(Path.cwd())
    if pddrc_path:
        try:
            config = _load_pddrc_config(pddrc_path)
            contexts = config.get("contexts", {})
            default_context = contexts.get("default", {})
            default_budget = default_context.get("defaults", {}).get("budget")
            if default_budget is not None:
                resolved_budget = float(default_budget)
                if resolved_budget > 0:
                    return resolved_budget
        except (TypeError, ValueError):
            pass

    return DEFAULT_SYNC_BUDGET


def _resolve_global_sync_target_coverage(target_coverage: Optional[float]) -> Optional[float]:
    """Resolve no-argument global sync target coverage from CLI or .pddrc."""
    if target_coverage is not None:
        return target_coverage

    pddrc_path = _find_pddrc_file(Path.cwd())
    if pddrc_path:
        try:
            config = _load_pddrc_config(pddrc_path)
            contexts = config.get("contexts", {})
            default_context = contexts.get("default", {})
            default_target = default_context.get("defaults", {}).get("target_coverage")
            if default_target is not None:
                resolved_target = float(default_target)
                if resolved_target >= 0:
                    return resolved_target
        except (TypeError, ValueError):
            pass

    return None


def _parse_boolish(value: Any) -> Optional[bool]:
    if isinstance(value, bool):
        return value
    if value is None:
        return None
    text = str(value).strip().lower()
    if text in {"1", "true", "yes", "on"}:
        return True
    if text in {"0", "false", "no", "off"}:
        return False
    return None


def _resolve_compressed_context(cli_value: Optional[bool]) -> bool:
    """Resolve compressed-context enablement from CLI, .pddrc, then default false."""
    if cli_value is not None:
        return cli_value
    pddrc_path = _find_pddrc_file(Path.cwd())
    if pddrc_path:
        try:
            config = _load_pddrc_config(pddrc_path)
            contexts = config.get("contexts", {})
            default_context = contexts.get("default", {})
            resolved = _parse_boolish(default_context.get("defaults", {}).get("compressed_context"))
            if resolved is not None:
                return resolved
        except (TypeError, ValueError):
            pass
    return False


def _compression_from_sync_result(result: Mapping[str, Any]) -> Optional[Mapping[str, Any]]:
    compression = result.get("compression")
    if isinstance(compression, Mapping):
        return compression
    phases: list[Any] = []
    for phase_result in result.get("results_by_language", {}).values() if isinstance(result.get("results_by_language"), Mapping) else []:
        if isinstance(phase_result, Mapping) and isinstance(phase_result.get("compression"), Mapping):
            phases.append(phase_result["compression"])
    if phases:
        return {"enabled": True, "languages": phases}
    return None


def _agentic_fallback_from_sync_result(result: Mapping[str, Any]) -> Optional[Mapping[str, Any]]:
    fallback = result.get("agentic_fallback")
    return fallback if isinstance(fallback, Mapping) else None


def _echo_architecture_sync_result(result: Dict[str, Any], *, dry_run: bool) -> None:
    """Render a concise summary for prompt-to-architecture sync."""
    summary = (
        f"Dry run: would update {result['updated_count']} module(s); "
        f"skipped {result['skipped_count']}."
        if dry_run
        else f"Updated {result['updated_count']} module(s); skipped {result['skipped_count']}."
    )
    click.echo(summary)

    total_rules = 0
    total_stories = 0
    has_contracts = False
    for entry in result.get("results", []):
        summary_data = entry.get("contract_summary")
        if summary_data:
            has_contracts = True
            total_rules += len(summary_data.get("rules", []))
            total_stories += len(summary_data.get("stories", []))

    if has_contracts:
        click.echo(
            f"Total contracts: {total_rules} rules, {total_stories} stories "
            "across synced modules."
        )

    for entry in result.get("results", []):
        if entry.get("updated"):
            click.echo(f"UPDATED {entry['filename']}")
            summary_data = entry.get("contract_summary")
            if summary_data:
                click.echo(
                    f"  Contracts: {len(summary_data.get('rules', []))} rules, "
                    f"{len(summary_data.get('stories', []))} stories"
                )
                ev_status = summary_data.get("evidence_status")
                if ev_status == "stale":
                    click.echo(
                        click.style(
                            f"  Warning: evidence is stale for {entry['filename']}",
                            fg="yellow",
                        )
                    )
                elif ev_status == "missing" and summary_data.get("rules"):
                    click.echo(
                        click.style(
                            f"  Warning: evidence is missing for {entry['filename']}",
                            fg="red",
                        )
                    )
                elif ev_status == "error":
                    click.echo(
                        click.style(
                            f"  Warning: evidence status error for {entry['filename']}",
                            fg="yellow",
                        )
                    )
        elif not entry.get("success"):
            click.echo(f"ERROR {entry['filename']}: {entry.get('error')}")
        for warning in entry.get("warnings", []):
            click.echo(f"WARNING {entry['filename']}: {warning}")

    for filename in result.get("registered", []):
        click.echo(f"REGISTERED {filename}")

    sync_errors = result.get("errors", [])
    validation = result.get("validation", {})
    validation_errors = validation.get("errors", [])
    validation_warnings = validation.get("warnings", [])

    if sync_errors:
        click.echo("Sync errors:")
        for error in sync_errors:
            click.echo(f"- {error}")

    if validation_errors:
        click.echo("Validation errors:")
        for error in validation_errors:
            click.echo(f"- {error['message']}")

    if validation_warnings:
        click.echo("Validation warnings:")
        for warning in validation_warnings:
            click.echo(f"- {warning['message']}")


@click.command("sync-architecture")
@click.argument("filenames", nargs=-1)
@click.option(
    "--dry-run",
    is_flag=True,
    default=False,
    help="Analyze prompt-to-architecture sync without writing architecture.json.",
)
@click.pass_context
@track_cost
def sync_architecture(
    ctx: click.Context,
    filenames: Tuple[str, ...],
    dry_run: bool,
) -> Optional[Tuple[Dict[str, Any], float, str]]:
    """Sync architecture.json from prompt metadata tags."""
    ctx.ensure_object(dict)
    quiet = ctx.obj.get("quiet", False)

    try:
        result = sync_prompts_to_architecture(
            filenames=list(filenames) or None,
            dry_run=dry_run,
        )

        if not quiet:
            _echo_architecture_sync_result(result, dry_run=dry_run)

        if not result.get("success"):
            raise click.exceptions.Exit(1)

        return result, 0.0, "local"
    except click.Abort:
        raise
    except click.exceptions.Exit:
        raise
    except Exception as exception:
        handle_error(exception, "sync-architecture", quiet)
        return None


@click.command("auto-deps")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False))
# exists=False to allow manual handling of quoted paths or paths with globs that shell didn't expand
@click.argument("directory_path", type=click.Path(exists=False, file_okay=False))
@click.option(
    "--output",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the modified prompt (file or directory).",
)
@click.option(
    "--csv",
    type=click.Path(writable=True),
    default=None,
    help="Specify the CSV file that contains or will contain dependency information.",
)
@click.option(
    "--force-scan",
    is_flag=True,
    default=False,
    help="Force rescanning of all potential dependency files even if they exist in the CSV file.",
)
@click.option(
    "--include-docs",
    is_flag=True,
    default=False,
    help="Include documentation files (.md, .txt, .rst) in dependency discovery.",
)
@click.option(
    "--no-dedup",
    is_flag=True,
    default=False,
    help="Skip redundant inline content removal after inserting includes.",
)
@click.option(
    "--concurrency",
    type=int,
    default=1,
    help="Maximum number of parallel LLM calls for dependency analysis (default: 1).",
)
@click.option(
    "--compress",
    is_flag=True,
    default=False,
    help=(
        "Tag discovered Python dependencies with mode=\"compressed\" for "
        "few-shot context reduction."
    ),
)
@click.pass_context
@track_cost
def auto_deps(
    ctx: click.Context,
    prompt_file: str,
    directory_path: str,
    output: Optional[str],
    csv: Optional[str],
    force_scan: bool,
    include_docs: bool,
    no_dedup: bool,
    concurrency: int,
    compress: bool,
) -> Optional[Tuple[str, float, str]]:
    """Analyze project dependencies and update the prompt file."""
    try:
        # Strip quotes from directory_path if present (e.g. passed incorrectly)
        if directory_path:
            directory_path = directory_path.strip('"').strip("'")

        # Pass additional options via ctx.obj for downstream consumption
        ctx.ensure_object(dict)
        ctx.obj["include_docs"] = include_docs
        ctx.obj["no_dedup"] = no_dedup
        ctx.obj["concurrency"] = concurrency

        result, total_cost, model_name = auto_deps_main(
            ctx=ctx,
            prompt_file=prompt_file,
            directory_path=directory_path,
            auto_deps_csv_path=csv,
            output=output,
            force_scan=force_scan,
            include_docs=include_docs,
            no_dedup=no_dedup,
            concurrency=concurrency,
            compress=compress,
        )
        return result, total_cost, model_name
    except click.Abort:
        raise
    except FingerprintFinalizeError as exception:
        raise click.ClickException(str(exception)) from exception
    except Exception as exception:
        handle_error(exception, "auto-deps", ctx.obj.get("quiet", False))
        return None


@click.command("setup")
@click.pass_context
def setup(ctx: click.Context):
    """Run the interactive setup utility."""
    try:
        # Import here to allow proper mocking
        from .. import cli as cli_module
        quiet = ctx.obj.get("quiet", False) if ctx.obj else False
        # First install completion
        cli_module.install_completion(quiet=quiet)
        # Then run setup utility
        _run_setup_utility()
    except Exception as e:
        handle_error(e, "setup", False)
