"""
Checkup command — GitHub issue-driven project health check, or local diagnostics.
"""
import click
from pathlib import Path
from typing import Optional, Tuple

from ..agentic_change import _parse_pr_url
from ..agentic_checkup import run_agentic_checkup
from ..agentic_sync import _is_github_issue_url
from ..track_cost import track_cost
from ..core.errors import handle_error


@click.command("checkup")
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
        "PR-mode: verify this existing pull request instead of creating a new one. "
        "Requires --issue. TARGET must NOT be passed."
    ),
)
@click.option(
    "--issue",
    "issue_url_opt",
    type=str,
    default=None,
    help=(
        "PR-mode companion to --pr: the original GitHub issue the PR is meant to "
        "resolve. Used as issue context for verification."
    ),
)
@click.option(
    "--review-loop",
    is_flag=True,
    default=False,
    help="In PR mode, run the multi-reviewer review/fix loop before returning a verdict.",
)
@click.option(
    "--reviewers",
    type=str,
    default="codex,claude",
    show_default=True,
    help="Comma-separated reviewer roles for --review-loop.",
)
@click.option(
    "--max-review-rounds",
    type=int,
    default=5,
    show_default=True,
    help="Maximum reviewer/fixer ping-pong rounds.",
)
@click.option(
    "--max-review-cost",
    type=float,
    default=10.0,
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
    help="Require every configured reviewer to be clean before ship.",
)
@click.option(
    "--continue-on-reviewer-limit",
    is_flag=True,
    default=False,
    help="Continue after a reviewer hits a provider/rate/context limit, marking degraded.",
)
@click.option(
    "--require-final-fresh-review/--no-require-final-fresh-review",
    default=True,
    show_default=True,
    help="Require a fresh final review after the last fix.",
)
@click.pass_context
@track_cost
def checkup(
    ctx: click.Context,
    target: Optional[str],
    validate_arch_includes: bool,
    project_root: Optional[Path],
    strict: bool,
    no_fix: bool,
    timeout_adder: float,
    no_github_state: bool,
    pr_url: Optional[str],
    issue_url_opt: Optional[str],
    review_loop: bool,
    reviewers: str,
    max_review_rounds: int,
    max_review_cost: float,
    max_review_minutes: float,
    require_all_reviewers_clean: bool,
    continue_on_reviewer_limit: bool,
    require_final_fresh_review: bool,
) -> Optional[Tuple[str, float, str]]:
    """
    Run agentic health checkup from a GitHub issue, or local diagnostics.

    \b
    GitHub mode (default): TARGET is an issue URL.
    PR mode: pass --pr <pr-url> and --issue <issue-url> to verify an existing PR
             against its source issue without creating a new PR.
    Local mode: pass --validate-arch-includes (no TARGET) to cross-validate
    architecture.json entries against module prompt <include> tags.
    """
    ctx.ensure_object(dict)

    if validate_arch_includes:
        if target is not None or pr_url is not None or issue_url_opt is not None:
            raise click.BadParameter(
                "Do not pass TARGET, --pr, or --issue when using --validate-arch-includes.",
                param_hint="'TARGET'",
            )
        root = project_root if project_root is not None else Path.cwd()
        from ..architecture_include_validation import run_validate_arch_includes_cli

        run_validate_arch_includes_cli(root, strict=strict, quiet=ctx.obj.get("quiet", False))
        return "validate-arch-includes: ok", 0.0, ""

    # PR-mode argument validation
    pr_mode = pr_url is not None or issue_url_opt is not None
    if review_loop and not pr_mode:
        raise click.BadParameter(
            "--review-loop requires --pr and --issue.",
            param_hint="'--review-loop'",
        )
    if review_loop and no_fix:
        raise click.BadParameter(
            "--review-loop cannot be combined with --no-fix; the loop owns the fixer step.",
            param_hint="'--review-loop'",
        )
    if review_loop and max_review_rounds < 1:
        raise click.BadParameter(
            "--max-review-rounds must be >= 1.",
            param_hint="'--max-review-rounds'",
        )
    if review_loop and max_review_cost <= 0:
        raise click.BadParameter(
            "--max-review-cost must be > 0.",
            param_hint="'--max-review-cost'",
        )
    if review_loop and max_review_minutes <= 0:
        raise click.BadParameter(
            "--max-review-minutes must be > 0.",
            param_hint="'--max-review-minutes'",
        )
    if pr_mode:
        if target is not None:
            raise click.BadParameter(
                "Do not pass TARGET when using --pr/--issue; they are mutually exclusive.",
                param_hint="'TARGET'",
            )
        if pr_url is None or issue_url_opt is None:
            raise click.BadParameter(
                "--pr and --issue must both be provided in PR mode.",
                param_hint="'--pr/--issue'",
            )
        if _parse_pr_url(pr_url) is None:
            raise click.BadParameter(
                "--pr must be a GitHub pull-request URL "
                "(e.g., https://github.com/org/repo/pull/123).",
                param_hint="'--pr'",
            )
        if not _is_github_issue_url(issue_url_opt):
            raise click.BadParameter(
                "--issue must be a GitHub issue URL "
                "(e.g., https://github.com/org/repo/issues/123).",
                param_hint="'--issue'",
            )
        # PR mode without --no-fix would generate fix commits inside the
        # PR-mode worktree (.pdd/worktrees/checkup-pr-N/) and never push
        # them back to the PR — silently abandoning the work and confusing
        # the user (who sees "Checkup complete" with no indication that
        # fixes exist on a local branch). Push-back is a separate follow-up;
        # until it lands, force --no-fix when --pr is set and warn so the
        # user can re-invoke without --pr if they wanted fixes applied.
        if not no_fix and not review_loop:
            click.echo(
                "Warning: --pr forces --no-fix because push-back to the PR "
                "is not yet implemented. Generated fixes inside the PR "
                "worktree would not reach the PR. Re-invoke without --pr "
                "(or with an issue TARGET) to apply fixes.",
                err=True,
            )
            no_fix = True
        effective_issue_url = issue_url_opt
    else:
        if not target:
            raise click.UsageError(
                "Missing argument 'TARGET'. For local checks use "
                "`pdd checkup --validate-arch-includes`. For PR verification use "
                "`pdd checkup --pr <pr-url> --issue <issue-url>`."
            )

        if not _is_github_issue_url(target):
            raise click.BadParameter(
                "TARGET must be a GitHub issue URL "
                "(e.g., https://github.com/org/repo/issues/123), "
                "or use --pr/--issue for PR verification, "
                "or --validate-arch-includes for architecture / include validation.",
                param_hint="'TARGET'",
            )
        effective_issue_url = target

    quiet = ctx.obj.get("quiet", False)
    verbose = ctx.obj.get("verbose", False)

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
            review_loop=review_loop,
            reviewers=reviewers,
            max_review_rounds=max_review_rounds,
            max_review_cost=max_review_cost,
            max_review_minutes=max_review_minutes,
            require_all_reviewers_clean=require_all_reviewers_clean,
            continue_on_reviewer_limit=continue_on_reviewer_limit,
            require_final_fresh_review=require_final_fresh_review,
        )

        if not quiet:
            status = "Success" if success else "Failed"
            click.echo(f"Status: {status}")
            click.echo(f"Message: {message}")
            click.echo(f"Cost: ${cost:.4f}")
            click.echo(f"Model: {model}")

        if not success:
            raise click.exceptions.Exit(1)

        return message, cost, model

    except (click.Abort, click.exceptions.Exit):
        raise
    except Exception as exception:
        handle_error(exception, "checkup", ctx.obj.get("quiet", False))
        return None
