"""
Checkup command — GitHub issue-driven project health check, or local diagnostics.
"""
# pylint: disable=unknown-option-value
import math
import sys
from pathlib import Path
from typing import Optional, Tuple

import click

from ..agentic_change import _parse_pr_url
from ..agentic_checkup import run_agentic_checkup
from ..checkup_prompt_main import build_prompt_source_set_report, run_checkup_prompt
from ..checkup_target import (
    CheckupTargetKind,
    classify_checkup_target,
    is_prompt_shaped_target,
)
from ..prompt_repair import (
    PromptRepairConfig,
    discover_prompt_paths,
    format_token_delta_summary,
    load_prompt_repair_defaults,
    run_prompt_repair_loop,
)
from ..agentic_sync import _is_github_issue_url
from ..track_cost import track_cost
from ..core.errors import handle_error
from ..core.utils import echo_model_line
from .checkup_simplify import checkup_simplify
from .checkup_snapshot import checkup_snapshot
from .contracts import contracts_check, contracts_cli
from .coverage import coverage_cmd
from .gate import gate_cmd
from .drift import drift_cmd
from .prompt import prompt_lint


def _interactive_tty_available() -> bool:
    """Return True when stdin and stdout are interactive terminals."""
    return sys.stdin.isatty() and sys.stdout.isatty()


def _forward_subcommand_json(
    args: list[str],
    *,
    as_json: bool,
    after: Optional[str] = None,
) -> list[str]:
    """Forward parent ``--json`` to focused checkup subcommands."""
    if not as_json or "--json" in args:
        return list(args)
    forwarded = list(args)
    if after is not None and after in forwarded:
        forwarded.insert(forwarded.index(after) + 1, "--json")
    else:
        forwarded.insert(0, "--json")
    return forwarded


@click.command(
    "checkup",
    context_settings={"ignore_unknown_options": True, "allow_extra_args": True},
    add_help_option=False,
)
@click.argument("target", required=False, default=None)
@click.option(
    "--validate-arch-includes",
    "validate_arch_includes",
    is_flag=True,
    default=False,
    help="Cross-check architecture.json against module <include> tags (no GitHub issue).",
)
@click.option(
    "--project-root",
    "project_root",
    type=click.Path(exists=True, path_type=Path, file_okay=False),
    default=None,
    help="With --validate-arch-includes: directory to scan (default: current directory).",
)
@click.option(
    "--strict",
    is_flag=True,
    default=False,
    help="With --validate-arch-includes: also validate bundled sample trees (examples/, …).",
)
@click.option(
    "--no-fix",
    is_flag=True,
    default=False,
    help="Report only, don't apply fixes.",
)
@click.option(
    "--timeout-adder",
    type=float,
    default=0.0,
    help="Additional seconds to add to each step's timeout.",
)
@click.option(
    "--start-step",
    "start_step",
    type=click.Choice(["1", "2", "3", "4", "5", "6.1", "6.2", "6.3", "7", "8"]),
    default=None,
    help="Recovery override: start the legacy checkup workflow from this step.",
)
@click.option(
    "--no-github-state",
    is_flag=True,
    default=False,
    help="Disable GitHub state persistence.",
)
@click.option(
    "--pr",
    "pr_url",
    type=str,
    default=None,
    help=(
        "PR-mode: run the full checkup against this existing pull request "
        "instead of creating a new one. Unless --no-fix is set, eligible "
        "generated fixes are committed and pushed back to the PR head ref. "
        "With no --issue the PR is reviewed on its own merits. TARGET must "
        "NOT be passed."
    ),
)
@click.option(
    "--issue",
    "issue_url_opt",
    type=str,
    default=None,
    help=(
        "Optional PR-mode companion to --pr: the original GitHub issue the PR "
        "is meant to resolve. When provided, the PR is also verified for "
        "issue alignment; when omitted, the PR is reviewed on its own merits. "
        "Required with --review-loop. Cannot be passed without --pr."
    ),
)
@click.option(
    "--test-scope",
    "test_scope",
    type=click.Choice(["full", "targeted"]),
    default="full",
    show_default=True,
    help=(
        "PR-mode test scope. 'full' (default) runs the full discovered "
        "test suite in Step 5 and Step 7. 'targeted' is an opt-in fast "
        "path that passes PR changed-file context into Steps 5/7 so the "
        "agent runs PR-scoped tests only; the final report explicitly "
        "labels verification as targeted (full suite not run). Only "
        "meaningful with --pr."
    ),
)
@click.option(
    "--full-suite-source",
    "full_suite_source",
    type=click.Choice(["local", "github-checks"]),
    default="local",
    show_default=True,
    help=(
        "Final-gate full-suite source. 'local' requires --test-scope full and "
        "uses Layer 1 local full-suite evidence. 'github-checks' requires "
        "--test-scope targeted and gates on GitHub checks for the current PR "
        "head before Layer 2."
    ),
)
@click.option(
    "--review-loop",
    is_flag=True,
    default=False,
    help="In PR mode, run the primary-reviewer/fixer loop before returning a verdict.",
)
@click.option(
    "--final-gate",
    "final_gate",
    is_flag=True,
    default=False,
    help=(
        "Canonical final PR gate (issue #1406). Requires --pr and --issue. "
        "Runs the PR-scoped checkup (Layer 1, no new PR) then the "
        "reviewer/fixer review-loop (Layer 2) on the resulting PR head, and "
        "returns a real ship verdict (exit non-zero unless the PR is "
        "shippable). This is what \"ready for maintainer review\" means once a "
        "PR exists. Cannot be combined with --review-loop, --no-fix, "
        "--review-only, --start-step, --no-gates, or --test-scope targeted "
        "unless --full-suite-source github-checks is also set."
    ),
)
@click.option(
    "--review-only",
    is_flag=True,
    default=False,
    help=(
        "With --review-loop, run only the primary reviewer first pass and do "
        "not invoke the fixer, commit, or push."
    ),
)
@click.option(
    "--reviewers",
    type=str,
    default="codex,claude",
    show_default=True,
    help="Legacy comma-separated role order for --review-loop: reviewer,fixer.",
)
@click.option(
    "--reviewer",
    type=str,
    default=None,
    show_default=False,
    help="Primary reviewer role for --review-loop. Overrides the first --reviewers role.",
)
@click.option(
    "--fixer",
    type=str,
    default=None,
    show_default=False,
    help="Fixer role for --review-loop. Overrides the second --reviewers role.",
)
@click.option(
    "--reviewer-fallback",
    type=str,
    default=None,
    show_default=False,
    help=(
        "Optional secondary reviewer role to invoke once if the primary reviewer "
        "fails (auth/network/exec/sandbox/rate-limit). Must differ from --reviewer "
        "and --fixer."
    ),
)
@click.option(
    "--fixer-fallback",
    type=str,
    default=None,
    show_default=False,
    help=(
        "Optional secondary fixer role to invoke once if the primary fixer "
        "cannot address the reviewer's findings (e.g. a subscription-tier "
        "credential exhaustion such as Claude Code 'You've hit your limit "
        "· resets …'). Must differ from --fixer and --reviewer to preserve "
        "reviewer/fixer role independence."
    ),
)
@click.option(
    "--max-review-rounds",
    type=int,
    default=5,
    show_default=True,
    help="Maximum primary-reviewer/fixer rounds.",
)
@click.option(
    "--max-review-cost",
    type=float,
    default=50.0,
    show_default=True,
    help="Maximum review-loop LLM cost in USD.",
)
@click.option(
    "--max-review-minutes",
    type=float,
    default=90.0,
    show_default=True,
    help="Maximum wall-clock minutes for the review loop.",
)
@click.option(
    "--require-all-reviewers-clean/--no-require-all-reviewers-clean",
    default=True,
    show_default=True,
    help="Compatibility flag; the primary reviewer is the authoritative ship gate.",
)
@click.option(
    "--continue-on-reviewer-limit",
    is_flag=True,
    default=False,
    help=(
        "Report provider/rate/context-limit/auth/network/sandbox reviewer "
        "failures as degraded instead of failed. This never marks an active "
        "reviewer clean or continues mutation without a completed review."
    ),
)
@click.option(
    "--require-final-fresh-review/--no-require-final-fresh-review",
    default=True,
    show_default=True,
    help="Compatibility flag; the primary reviewer's clean verification is final.",
)
@click.option(
    "--blocking-severities",
    type=str,
    default=None,
    show_default=False,
    help=(
        "Comma-separated highest-priority severities for review-loop reporting "
        "and prompt guidance. The fixer still receives every valid reviewer "
        "finding. Default: blocker,critical,medium. Unknown severities are dropped."
    ),
)
@click.option(
    "--clean-reviewer-states",
    type=str,
    default=None,
    show_default=False,
    help=(
        "Compatibility parser for downstream reviewer-status gates. Default: "
        "clean. The tokens 'failed', 'degraded', and 'missing' are always "
        "treated as not-clean regardless of this flag."
    ),
)
@click.option(
    "--fallback-reviewer-on-failure",
    is_flag=True,
    default=False,
    help=(
        "Opt-in. When the primary reviewer ends in 'failed' or 'missing' "
        "on the initial review pass of a round, run a second review pass "
        "using the configured fixer's identity as a fallback reviewer. "
        "On a clean fallback the rendered reviewer-status line shows the "
        "primary as clean so downstream verdict adapters do not short-"
        "circuit on the primary's outage; the original failure detail "
        "is preserved in the Reviewer Diagnostics block of the final "
        "report. NOTE: 'degraded' is intentionally NOT promoted — "
        "degraded means reduced quality (rate limit, context window, "
        "etc.) and must not silently lose signal. The fallback also does "
        "NOT trigger on the post-fix verification pass: the fixer just "
        "authored the changes being verified, so promoting it to "
        "verifier would collapse the reviewer/fixer independence."
    ),
)
@click.option(
    "--no-gates",
    "no_gates",
    is_flag=True,
    default=False,
    help=(
        "Disable the deterministic-gate enforcement layer (issue #1092). "
        "By default the review loop discovers a conservative set of fast "
        "local checks (prettier --check, git diff --check against the PR "
        "range, a non-mutating Python syntax check, optional "
        "ruff/black/mypy/tsc) and refuses a clean LLM verdict if "
        "any of them fail on the PR worktree. Pass --no-gates to fall "
        "back to LLM-only verdicts (legacy behavior); the loop will then "
        "trust the reviewer's clean even if a deterministic check would "
        "have failed locally."
    ),
)
@click.option(
    "--gate-timeout",
    "gate_timeout",
    type=float,
    default=60.0,
    show_default=True,
    help=(
        "Per-gate wall-clock timeout in seconds. A gate exceeding this "
        "cap is recorded as a runner-side failure (exit_code=None) and "
        "treated as a blocker finding rather than blocking the loop."
    ),
)
@click.option(
    "--gate-allow",
    "gate_allow",
    type=str,
    multiple=True,
    default=(),
    help=(
        "Repeatable. Forward-compatibility hook for opting extra gate "
        "names into discovery beyond the conservative v1 set. Each "
        "value is one gate name. Discovery remains allowlist-only; this "
        "argument is threaded through so the CLI and discovery surfaces "
        "can co-evolve without breaking signature stability."
    ),
)
@click.option(
    "--prompt-repair",
    type=click.Choice(["off", "best-effort", "strict"]),
    default=None,
    help=(
        "With prompt targets: run repair after a failed checkup, then re-check. "
        "Overrides pyproject.toml [tool.pdd.checkup].prompt_repair (default: off)."
    ),
)
@click.option(
    "--max-prompt-repair-rounds",
    type=int,
    default=None,
    help="Maximum repair-and-recheck iterations per prompt file (default: 1).",
)
@click.option(
    "--max-prompt-token-growth",
    type=int,
    default=None,
    help="Maximum token increase allowed during repair (default: 1000).",
)
@click.option(
    "--max-prompt-repair-seconds",
    type=float,
    default=None,
    help="Wall-clock timeout for the prompt repair loop in seconds (default: 120).",
)
@click.option(
    "--interactive",
    "interactive",
    is_flag=True,
    default=False,
    help="With .prompt targets: enter interactive per-finding repair session.",
)
@click.option(
    "--apply",
    "apply",
    is_flag=True,
    default=False,
    help=(
        "Write the selected low-risk repairs to the prompt, then re-verify. "
        "Requires --interactive or --auto. Without it, fixes are only queued/saved."
    ),
)
@click.option(
    "--dry-run",
    "--preview",
    "dry_run",
    is_flag=True,
    default=False,
    help=(
        "With --apply: preview the changes without writing any files. "
        "--preview is kept as a compatibility alias."
    ),
)
@click.option(
    "--planner",
    "planner",
    type=click.Choice(["deterministic", "llm"], case_sensitive=False),
    default=None,
    help=(
        "With --interactive: planning strategy for the agentic checkup session. "
        "'deterministic' (default) runs all tools in fixed order. "
        "'llm' asks an LLM to suggest which tools matter most."
    ),
)
@click.option(
    "--auto",
    "auto_mode",
    is_flag=True,
    default=False,
    help=(
        "Resolve every finding without per-finding prompts: low-risk fixes are "
        "queued (or written with --apply); medium-risk are saved for review; "
        "high-risk are left as manual TODOs. Nothing is written unless --apply."
    ),
)
@click.option(
    "--json",
    "as_json",
    is_flag=True,
    default=False,
    help="With prompt targets: emit ``pdd.prompt_source_set_report.v1`` JSON.",
)
@click.option(
    "--explain",
    is_flag=True,
    default=False,
    help="With prompt targets: read-only finding summary (non-fatal; no exit-code change).",
)
@click.option(
    "-h",
    "--help",
    "show_help",
    is_flag=True,
    is_eager=True,
    default=False,
    help="Show this message and exit.",
)
@click.pass_context
@track_cost
def checkup(  # pylint: disable=too-many-arguments,too-many-positional-arguments,too-many-locals,too-many-branches,too-many-statements,too-many-return-statements,unknown-option-value
    ctx: click.Context,
    target: Optional[str],
    show_help: bool,
    validate_arch_includes: bool,
    project_root: Optional[Path],
    strict: bool,
    as_json: bool,
    explain: bool,
    no_fix: bool,
    timeout_adder: float,
    start_step: Optional[str],
    no_github_state: bool,
    pr_url: Optional[str],
    issue_url_opt: Optional[str],
    test_scope: str,
    full_suite_source: str,
    review_loop: bool,
    final_gate: bool,
    review_only: bool,
    reviewers: str,
    reviewer: Optional[str],
    fixer: Optional[str],
    reviewer_fallback: Optional[str],
    fixer_fallback: Optional[str],
    max_review_rounds: int,
    max_review_cost: float,
    max_review_minutes: float,
    require_all_reviewers_clean: bool,
    continue_on_reviewer_limit: bool,
    require_final_fresh_review: bool,
    blocking_severities: Optional[str],
    clean_reviewer_states: Optional[str],
    fallback_reviewer_on_failure: bool,
    no_gates: bool,
    gate_timeout: float,
    gate_allow: Tuple[str, ...],
    prompt_repair: Optional[str],
    max_prompt_repair_rounds: Optional[int],
    max_prompt_token_growth: Optional[int],
    max_prompt_repair_seconds: Optional[float],
    interactive: bool,
    apply: bool,
    dry_run: bool,
    planner: Optional[str],
    auto_mode: bool,
) -> Optional[Tuple[str, float, str]]:
    """
    pdd checkup = verifier namespace

    Run agentic health checkup from a GitHub issue, or local prompt diagnostics.

    \b
    Prompt targets (source-set health):
      pdd checkup prompts/foo_python.prompt
      pdd checkup prompts/
      pdd checkup <devunit>
          → Is this prompt source-set clear, covered, evidenced, and ready to generate from?
    Focused prompt checks (CI / debugging):
      pdd checkup lint ...
      pdd checkup contract check ...
      pdd checkup coverage ...
      pdd checkup gate ...
      pdd checkup snapshot ...
      pdd checkup drift ...
    Issue / PR checkup:
      pdd checkup <issue-url>
      pdd checkup --pr <pr-url>

    GitHub mode (default): TARGET is an issue URL.
    PR mode: pass --pr <pr-url> to run the full checkup against an existing
             PR. With no --issue the PR is reviewed on its own merits;
             add --issue <issue-url> to also verify the PR resolves that
             issue. Unless --no-fix is set, the fix/verify loop runs against
             the PR worktree and any eligible generated fixes are committed
             and pushed back to the PR head ref. Step 8 (create PR) is
             skipped — no second PR is opened.
    Local mode: pass --validate-arch-includes (no TARGET) to cross-validate
    architecture.json entries against module prompt <include> tags.
    Simplify (Claude Code /simplify, requires --apply):
      pdd checkup simplify [PATH] [OPTIONS]
    Prompt lint:
      pdd checkup lint TARGET [OPTIONS]  →  lint prompts and user stories for quality and ambiguity.
    Contract checks:
      pdd checkup contract check TARGET [OPTIONS]  (alias: ``pdd checkup contracts check``)
    Contract coverage:
      pdd checkup coverage [OPTIONS] TARGET
    Snapshot policy (nondeterministic prompt context):
      pdd checkup snapshot PROMPT_FILE [OPTIONS]
    Evidence and waiver gate:
      pdd checkup gate [TARGET] [OPTIONS]  →  evidence manifests and waiver policy.
    Regeneration drift:
      pdd checkup drift <DEVUNIT> [OPTIONS]
    """
    ctx.ensure_object(dict)

    if apply and not (interactive or auto_mode):
        raise click.UsageError("--apply requires --interactive or --auto.")

    # --auto runs the agentic session with no per-finding prompts, so it is safe
    # without a terminal (CI / scripted demo replay). Only a genuinely
    # prompt-driven interactive session requires a real TTY.
    if interactive and not auto_mode and not _interactive_tty_available():
        raise click.UsageError(
            "--interactive requires a TTY (stdin and stdout must be a terminal). "
            "Use --auto for a non-interactive agentic session."
        )

    if interactive and as_json:
        raise click.UsageError("--interactive cannot be combined with --json.")

    if show_help and target not in {
        "lint",
        "contract",
        "contracts",
        "coverage",
        "drift",
        "gate",
        "simplify",
        "snapshot",
    }:
        click.echo(ctx.command.get_help(ctx))
        return None

    if target in {"contract", "contracts"}:
        contract_args = _forward_subcommand_json(
            list(ctx.args),
            as_json=as_json,
            after="check",
        )
        if strict:
            # Forward strict to the subcommand scope, not the group scope.
            if contract_args and contract_args[0] == "check":
                contract_args.insert(1, "--strict")
            else:
                contract_args.insert(0, "--strict")
        if not contract_args:
            click.echo(
                contracts_cli.get_help(
                    click.Context(contracts_cli, info_name=f"pdd checkup {target}")
                )
            )
            return None
        if show_help:
            # Parent command owns -h/--help; explicitly render nested help.
            if contract_args[:1] == ["check"]:
                exit_code = contracts_check.main(
                    args=["--help"],
                    prog_name=f"pdd checkup {target} check",
                    standalone_mode=False,
                    obj=ctx.obj,
                )
                if exit_code:
                    raise click.exceptions.Exit(exit_code)
                return None
            contract_args.append("--help")
        if contract_args[0] == "check" and "--help" in contract_args[1:]:
            exit_code = contracts_check.main(
                args=["--help"],
                prog_name=f"pdd checkup {target} check",
                standalone_mode=False,
                obj=ctx.obj,
            )
            if exit_code:
                raise click.exceptions.Exit(exit_code)
            return None
        exit_code = contracts_cli.main(
            args=contract_args,
            prog_name=f"pdd checkup {target}",
            standalone_mode=False,
            obj=ctx.obj,
        )
        if exit_code:
            raise click.exceptions.Exit(exit_code)
        return None

    if target == "simplify":
        simplify_args = list(ctx.args)
        if show_help:
            simplify_args.append("--help")
        exit_code = checkup_simplify.main(
            args=simplify_args,
            prog_name="pdd checkup simplify",
            standalone_mode=False,
            obj=ctx.obj,
        )
        if show_help:
            ctx.exit()
        if exit_code:
            raise click.exceptions.Exit(exit_code)
        return None

    if target == "snapshot":
        snapshot_args = _forward_subcommand_json(list(ctx.args), as_json=as_json)
        if not ctx.args or show_help:
            click.echo(
                checkup_snapshot.get_help(
                    click.Context(checkup_snapshot, info_name="pdd checkup snapshot")
                )
            )
            return None
        exit_code = checkup_snapshot.main(
            args=snapshot_args,
            prog_name="pdd checkup snapshot",
            standalone_mode=False,
            obj=ctx.obj,
        )
        if exit_code:
            raise click.exceptions.Exit(exit_code)
        return None

    if target == "lint":
        if not ctx.args or show_help:
            click.echo(
                prompt_lint.get_help(click.Context(prompt_lint, info_name="pdd checkup lint"))
            )
            return None
        lint_args = _forward_subcommand_json(list(ctx.args), as_json=as_json)
        if strict:
            lint_args.insert(0, "--strict")
        exit_code = prompt_lint.main(
            args=lint_args,
            prog_name="pdd checkup lint",
            standalone_mode=False,
            obj=ctx.obj,
        )
        if exit_code:
            raise click.exceptions.Exit(exit_code)
        return None

    if target == "coverage":
        if show_help:
            click.echo(
                coverage_cmd.get_help(click.Context(coverage_cmd, info_name="pdd checkup coverage"))
            )
            return None
        exit_code = coverage_cmd.main(
            args=_forward_subcommand_json(list(ctx.args), as_json=as_json),
            prog_name="pdd checkup coverage",
            standalone_mode=False,
            obj=ctx.obj,
        )
        if exit_code:
            raise click.exceptions.Exit(exit_code)
        return None

    if target == "gate":
        gate_args = _forward_subcommand_json(list(ctx.args), as_json=as_json)
        if show_help and not gate_args:
            click.echo(
                gate_cmd.get_help(click.Context(gate_cmd, info_name="pdd checkup gate"))
            )
            return None
        exit_code = gate_cmd.main(
            args=gate_args,
            prog_name="pdd checkup gate",
            standalone_mode=False,
            obj=ctx.obj,
        )
        if exit_code:
            raise click.exceptions.Exit(exit_code)
        return None

    if target == "drift":
        if not ctx.args or show_help:
            click.echo(
                drift_cmd.get_help(click.Context(drift_cmd, info_name="pdd checkup drift"))
            )
            return None
        drift_args = _forward_subcommand_json(list(ctx.args), as_json=as_json)
        exit_code = drift_cmd.main(
            args=drift_args,
            prog_name="pdd checkup drift",
            standalone_mode=False,
            obj=ctx.obj,
        )
        if exit_code:
            raise click.exceptions.Exit(exit_code)
        return None

    if ctx.args:
        raise click.UsageError(f"Got unexpected extra arguments ({' '.join(ctx.args)})")

    if validate_arch_includes:
        if target is not None or pr_url is not None or issue_url_opt is not None:
            raise click.BadParameter(
                "Do not pass TARGET, --pr, or --issue when using --validate-arch-includes.",
                param_hint="'TARGET'",
            )
        root = project_root if project_root is not None else Path.cwd()
        from ..architecture_include_validation import run_validate_arch_includes_cli  # pylint: disable=import-outside-toplevel

        run_validate_arch_includes_cli(root, strict=strict, quiet=ctx.obj.get("quiet", False))
        return "validate-arch-includes: ok", 0.0, ""

    target_kind = classify_checkup_target(target, project_root=project_root)

    if interactive and target is not None and not is_prompt_shaped_target(
        target,
        project_root=project_root,
    ):
        raise click.UsageError(
            "--interactive is only supported for prompt-shaped checkup targets."
        )

    if (
        pr_url is None
        and target is not None
        and is_prompt_shaped_target(target, project_root=project_root)
    ):
        _quiet = ctx.obj.get("quiet", False)
        _repair_defaults = load_prompt_repair_defaults(Path.cwd())
        _effective_repair = (
            prompt_repair if prompt_repair is not None else _repair_defaults.mode
        )
        _repair_active = _effective_repair not in (None, "off")
        _machine_output = as_json or explain

        # Agentic checkup is opt-in for prompt targets. Bare
        # `pdd checkup <prompt>` stays on the structured source-set path so the
        # issue #1423 interactive repair flow only runs after explicit intent.
        _single_prompt_file = target_kind == CheckupTargetKind.PROMPT_FILE
        _agent_requested = (
            _single_prompt_file
            and (interactive or planner is not None or auto_mode)
        ) and not _machine_output
        if _agent_requested:
            from ..checkup_agent import (  # pylint: disable=import-outside-toplevel
                MODE_AUTO,
                MODE_INTERACTIVE,
                MODE_REVIEW,
                CheckupAgent,
                TerminalCheckupSession,
            )
            from ..checkup_planner import make_planner  # pylint: disable=import-outside-toplevel

            _effective_planner = planner or "deterministic"
            if interactive and auto_mode:
                _mode = MODE_AUTO
            elif interactive:
                _mode = MODE_INTERACTIVE
            elif auto_mode:
                _mode = MODE_AUTO
            else:
                # --planner without --interactive: safe, non-interactive review.
                _mode = MODE_REVIEW

            _planner = make_planner(_effective_planner)
            _agent_session = TerminalCheckupSession(quiet=_quiet)
            _agent = CheckupAgent(_planner, _agent_session)
            return _agent.run(
                target,
                project_root=project_root,
                strict=strict,
                apply=apply,
                dry_run=dry_run,
                quiet=_quiet,
                explicit_interactive=interactive,
                auto=auto_mode,
                mode=_mode,
            )

        # Directory target: run the agentic review over every prompt and print
        # one aggregate pass/warn/block summary (one gate for the whole set).
        if (
            target_kind == CheckupTargetKind.PROMPT_DIRECTORY
            and not _machine_output
            and not _repair_active
        ):
            if interactive:
                raise click.UsageError(
                    "Interactive checkup runs on a single .prompt file. For a "
                    "directory, omit --interactive (review) or add --auto."
                )
            from ..checkup_agent import (  # pylint: disable=import-outside-toplevel
                MODE_AUTO,
                MODE_REVIEW,
                discover_prompt_files,
                run_checkup_directory,
            )
            from ..checkup_planner import make_planner  # pylint: disable=import-outside-toplevel

            _root = (project_root if project_root is not None else Path.cwd()).resolve()
            _raw_dir = Path(target)
            if _raw_dir.is_absolute():
                _dir = _raw_dir
            else:
                _rooted_dir = _root / target
                _dir = _rooted_dir if _rooted_dir.is_dir() else _raw_dir
            _files = discover_prompt_files(_dir)
            if not _files:
                raise click.UsageError(f"No .prompt files found under {target!r}.")
            return run_checkup_directory(
                make_planner(planner or "deterministic"),
                _files,
                project_root=_root.resolve(),
                strict=strict,
                apply=apply,
                auto=auto_mode,
                mode=MODE_AUTO if auto_mode else MODE_REVIEW,
                quiet=_quiet,
            )

        import json as _json  # pylint: disable=import-outside-toplevel

        quiet = _quiet

        passed, message, cost, model, exit_code = run_checkup_prompt(
            target,
            explain=explain,
            as_json=as_json,
            quiet=quiet or as_json,
            strict=strict,
            project_root=project_root,
        )

        # check → repair → recheck cycle (Issue #1422)
        # Repair runs only after a failed structured checkup and never with --json.
        if not passed and _effective_repair not in (None, "off") and not as_json:
            _root = project_root if project_root is not None else Path.cwd()
            _repair_cfg = PromptRepairConfig(
                mode=_effective_repair,
                max_rounds=(
                    max_prompt_repair_rounds if max_prompt_repair_rounds is not None
                    else _repair_defaults.max_rounds
                ),
                max_token_growth=(
                    max_prompt_token_growth if max_prompt_token_growth is not None
                    else _repair_defaults.max_token_growth
                ),
                max_seconds=(
                    max_prompt_repair_seconds if max_prompt_repair_seconds is not None
                    else _repair_defaults.max_seconds
                ),
            )
            _target_path = Path(target)
            if _target_path.is_file() and _target_path.suffix == ".prompt":
                _prompt_paths = [_target_path]
            else:
                _prompt_paths = discover_prompt_paths(_root)
            for _pp in _prompt_paths:
                # Feed the full structured report (coverage/contract/gate findings,
                # recommended_action) as repair context, not just lint.
                _report = build_prompt_source_set_report(
                    _pp,
                    target=target,
                    project_root=_root,
                    strict=strict,
                )
                # Mirror agentic_checkup.py: skip prompts that already pass so
                # we never invoke the LLM for info-only or non-actionable findings.
                if _report.status == "pass":
                    continue
                _repair_context = {
                    "source_set_report": _json.dumps(_report.as_dict(), indent=2),
                    "recommended_actions": "\n".join(_report.recommended_actions()),
                }
                _rr = run_prompt_repair_loop(
                    _pp, _repair_cfg, context=_repair_context, cwd=_root,
                    verbose=ctx.obj.get("verbose", False), quiet=quiet,
                    strict=strict,
                )
                if not quiet:
                    _summary = format_token_delta_summary(_rr)
                    if _summary:
                        click.echo(_summary)
            # Re-check after repair
            passed, message, cost, model, exit_code = run_checkup_prompt(
                target,
                explain=explain,
                as_json=as_json,
                quiet=quiet or as_json,
                strict=strict,
                project_root=project_root,
            )

        if not quiet and not as_json:
            echo_model_line(model)
        if exit_code:
            raise click.exceptions.Exit(exit_code)
        return message, cost, model

    # PR-mode argument validation.
    #
    # Issue #1292: ``--issue`` is OPTIONAL in ``--pr`` mode. PR mode is keyed
    # solely on ``--pr``; with no ``--issue`` the PR is reviewed on its own
    # merits (the issue-alignment gate is skipped downstream). A lone
    # ``--issue`` (no ``--pr``) is rejected — a standalone issue belongs in
    # default issue mode as the positional TARGET, not the ``--pr`` companion.
    pr_mode = pr_url is not None
    if test_scope == "targeted" and not pr_mode:
        raise click.BadParameter(
            "--test-scope targeted requires --pr (PR mode).",
            param_hint="'--test-scope'",
        )
    if issue_url_opt is not None and pr_url is None:
        raise click.BadParameter(
            "--issue requires --pr. To check an issue directly, pass it as "
            "TARGET (e.g., `pdd checkup <issue-url>`).",
            param_hint="'--issue'",
        )
    # ``--review-loop`` still requires BOTH ``--pr`` and ``--issue``: the
    # reviewer/report path is issue-coupled, so review-loop-without-issue is
    # deferred as a follow-up (#1292 sanctions deferring it).
    if review_loop and (not pr_mode or issue_url_opt is None):
        raise click.BadParameter(
            "--review-loop requires --pr and --issue.",
            param_hint="'--review-loop'",
        )
    # ``--final-gate`` is the canonical two-layer PR-readiness gate (#1406). It
    # requires ``--pr`` and owns the review-loop as Layer 2, so it cannot be
    # combined with flags that would contradict or duplicate the two-layer
    # contract. ``--issue`` remains optional in PR mode; without it, the
    # issue-alignment gate is skipped.
    if final_gate:
        if not pr_mode:
            raise click.BadParameter(
                "--final-gate requires --pr and --issue.",
                param_hint="'--final-gate'",
            )
        if issue_url_opt is None:
            raise click.BadParameter(
                "--final-gate requires --pr and --issue.",
                param_hint="'--final-gate'",
            )
        if review_loop:
            raise click.BadParameter(
                "--final-gate already runs the review-loop as Layer 2; do not "
                "also pass --review-loop.",
                param_hint="'--final-gate'",
            )
        if no_fix:
            raise click.BadParameter(
                "--final-gate cannot be combined with --no-fix; the gate owns "
                "the fix/review steps.",
                param_hint="'--final-gate'",
            )
        if review_only:
            raise click.BadParameter(
                "--final-gate cannot be combined with --review-only.",
                param_hint="'--final-gate'",
            )
        if start_step is not None:
            raise click.BadParameter(
                "--start-step applies to the legacy checkup workflow, not "
                "--final-gate.",
                param_hint="'--final-gate'",
            )
        if no_gates:
            raise click.BadParameter(
                "--final-gate cannot be combined with --no-gates; the canonical "
                "ship verdict requires the deterministic local gates, otherwise "
                "an LLM-only review could pass over a failing gate.",
                param_hint="'--final-gate'",
            )
        if full_suite_source == "github-checks" and test_scope != "targeted":
            raise click.BadParameter(
                "--full-suite-source github-checks requires --test-scope targeted; "
                "GitHub checks provide the full-suite truth.",
                param_hint="'--full-suite-source'",
            )
        if full_suite_source == "local" and test_scope != "full":
            raise click.BadParameter(
                "--final-gate requires full test scope; --test-scope targeted "
                "would return a ship verdict without running the full suite. "
                "Use --full-suite-source github-checks to pair targeted Layer 1 "
                "tests with GitHub checks.",
                param_hint="'--final-gate'",
            )
    if review_loop and start_step is not None:
        raise click.BadParameter(
            "--start-step applies to the legacy checkup workflow, not --review-loop.",
            param_hint="'--start-step'",
        )
    if review_only and not review_loop:
        raise click.BadParameter(
            "--review-only requires --review-loop.",
            param_hint="'--review-only'",
        )
    if review_loop and no_fix and not review_only:
        raise click.BadParameter(
            "--review-loop cannot be combined with --no-fix; the loop owns the fixer step.",
            param_hint="'--review-loop'",
        )
    # The final gate runs the review loop as Layer 2, so its budget knobs must
    # be valid there too — otherwise the canonical gate could terminate via a
    # runtime cap path (e.g. "Max review rounds reached: 0").
    if (review_loop or final_gate) and max_review_rounds < 1:
        raise click.BadParameter(
            "--max-review-rounds must be >= 1.",
            param_hint="'--max-review-rounds'",
        )
    if (review_loop or final_gate) and (
        not math.isfinite(max_review_cost) or max_review_cost <= 0
    ):
        raise click.BadParameter(
            "--max-review-cost must be a finite value > 0.",
            param_hint="'--max-review-cost'",
        )
    if (review_loop or final_gate) and (
        not math.isfinite(max_review_minutes) or max_review_minutes <= 0
    ):
        raise click.BadParameter(
            "--max-review-minutes must be a finite value > 0.",
            param_hint="'--max-review-minutes'",
        )
    if pr_mode:
        if target is not None:
            raise click.BadParameter(
                "Do not pass TARGET when using --pr/--issue; they are mutually exclusive.",
                param_hint="'TARGET'",
            )
        if _parse_pr_url(pr_url) is None:
            raise click.BadParameter(
                "--pr must be a GitHub pull-request URL "
                "(e.g., https://github.com/org/repo/pull/123).",
                param_hint="'--pr'",
            )
        # ``--issue`` is optional; validate its format only when supplied.
        if issue_url_opt is not None and not _is_github_issue_url(issue_url_opt):
            raise click.BadParameter(
                "--issue must be a GitHub issue URL "
                "(e.g., https://github.com/org/repo/issues/123).",
                param_hint="'--issue'",
            )
        # May be ``None`` → orchestrator reviews the PR on its own merits.
        effective_issue_url = issue_url_opt
    else:
        if not target:
            raise click.UsageError(
                "Missing argument 'TARGET'. For prompt source-set checks use "
                "`pdd checkup <file.prompt|prompts/|devunit>`. For local checks use "
                "`pdd checkup --validate-arch-includes`. To review a PR use "
                "`pdd checkup --pr <pr-url> [--issue <issue-url>]`."
            )

        if not _is_github_issue_url(target):
            raise click.BadParameter(
                "TARGET must be a GitHub issue URL "
                "(e.g., https://github.com/org/repo/issues/123), a prompt target "
                "(e.g., prompts/foo_python.prompt, prompts/, or a devunit name), "
                "or use --pr/--issue for PR verification, "
                "or --validate-arch-includes for architecture / include validation.",
                param_hint="'TARGET'",
            )
        effective_issue_url = target

    quiet = ctx.obj.get("quiet", False)
    verbose = ctx.obj.get("verbose", False)
    repair_defaults = load_prompt_repair_defaults(Path.cwd())
    effective_prompt_repair = (
        prompt_repair if prompt_repair is not None else repair_defaults.mode
    )
    effective_max_repair_rounds = (
        max_prompt_repair_rounds
        if max_prompt_repair_rounds is not None
        else repair_defaults.max_rounds
    )
    effective_max_token_growth = (
        max_prompt_token_growth
        if max_prompt_token_growth is not None
        else repair_defaults.max_token_growth
    )
    effective_max_repair_seconds = (
        max_prompt_repair_seconds
        if max_prompt_repair_seconds is not None
        else repair_defaults.max_seconds
    )
    start_step_override = None
    if start_step is not None:
        start_step_override = float(start_step)
        if start_step_override.is_integer():
            start_step_override = int(start_step_override)

    try:
        success, message, cost, model = run_agentic_checkup(
            issue_url=effective_issue_url,
            verbose=verbose,
            quiet=quiet,
            no_fix=no_fix,
            timeout_adder=timeout_adder,
            use_github_state=not no_github_state,
            reasoning_time=ctx.obj.get("time") if ctx.obj.get("time_explicit") else None,
            pr_url=pr_url,
            test_scope=test_scope,
            full_suite_source=full_suite_source,
            start_step_override=start_step_override,
            review_loop=review_loop,
            final_gate=final_gate,
            review_only=review_only,
            reviewers=reviewers,
            reviewer=reviewer,
            fixer=fixer,
            reviewer_fallback=reviewer_fallback,
            fixer_fallback=fixer_fallback,
            max_review_rounds=max_review_rounds,
            max_review_cost=max_review_cost,
            max_review_minutes=max_review_minutes,
            require_all_reviewers_clean=require_all_reviewers_clean,
            continue_on_reviewer_limit=continue_on_reviewer_limit,
            require_final_fresh_review=require_final_fresh_review,
            blocking_severities=blocking_severities,
            clean_reviewer_states=clean_reviewer_states,
            fallback_reviewer_on_failure=fallback_reviewer_on_failure,
            enable_gates=not no_gates,
            gate_timeout=gate_timeout,
            gate_allow=tuple(gate_allow),
            prompt_repair=effective_prompt_repair,
            max_prompt_repair_rounds=effective_max_repair_rounds,
            max_prompt_token_growth=effective_max_token_growth,
            max_prompt_repair_seconds=effective_max_repair_seconds,
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
    except Exception as exception:  # pylint: disable=broad-exception-caught
        handle_error(exception, "checkup", ctx.obj.get("quiet", False))
        return None
