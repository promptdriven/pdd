"""
One-session sync: run example, crash-fix, verify, test, and fix steps
in a single agentic session instead of separate sessions per step.
"""

import logging
import os
import sys
import threading
import time
from pathlib import Path
from typing import Any, Dict, List, Optional

from rich.console import Console
from rich import print as rprint

from .agentic_common import run_agentic_task
from .agentic_test_generate import (
    _get_file_mtimes,
    _snapshot_pre_test_contents,
)
from .code_generator_main import (
    PublicSurfaceRegressionError,
    TestChurnError,
    _env_flag_enabled,
    _get_test_churn_threshold,
    _is_test_output_path,
    _prompt_allows_test_churn,
    _verify_public_surface_regression,
    _verify_test_churn,
)
from .load_prompt_template import load_prompt_template
from .preprocess import preprocess

logger = logging.getLogger(__name__)
console = Console()


# Step display names for progress reporting
_STEP_DISPLAY = {
    "example_generate": "Example file created",
    "crash_fix": "Example runs without errors",
    "verify": "Behavior verified against spec",
    "test_generate": "Test file created",
    "test_pass": "All tests passing",
    "done": "All steps complete",
}

# Map one-session step markers to PDD_PHASE names that AsyncSyncRunner parses
_STEP_TO_PHASE = {
    "example_generate": "example",
    "crash_fix": "crash",
    "verify": "verify",
    "test_generate": "test",
    "done": "synced",
}

# Hard cap on test-churn retry attempts inside the one-session path. We never
# want more than one extra attempt regardless of how high
# ``MAX_CONFORMANCE_ATTEMPTS`` climbs in the orchestration runner — repeated
# agentic rewrites on the same prompt rarely converge and just burn cost.
# Exposed as a module-level constant so the short-circuit branch can be tested
# observably distinct from the natural exhaustion path (tests can
# ``monkeypatch.setattr`` to raise the cap without forcing this cap to follow).
_MAX_TEST_CHURN_ATTEMPTS = 2


def _read_new_progress(progress_file: Path, skip_count: int) -> List[str]:
    """Read new STEP_COMPLETE lines from the progress file, skipping already-reported ones."""
    if not progress_file.exists():
        return []
    try:
        content = progress_file.read_text(encoding="utf-8")
    except OSError:
        return []
    lines = [
        line.split("STEP_COMPLETE:", 1)[1].strip()
        for line in content.splitlines()
        if line.startswith("STEP_COMPLETE:")
    ]
    return lines[skip_count:]


def _format_step_display(step_name: str) -> str:
    """Convert a step marker name to a user-friendly display string."""
    if step_name in _STEP_DISPLAY:
        return _STEP_DISPLAY[step_name]
    if step_name.startswith("crash_fix_attempt:"):
        attempt = step_name.split(":")[1]
        return f"Crash fix attempt {attempt}"
    if step_name.startswith("test_fix_attempt:"):
        attempt = step_name.split(":")[1]
        return f"Test fix attempt {attempt}"
    return step_name


def _compute_import_base(code_path: Path, project_root: Path) -> str:
    """Compute the Python import base from the code file path relative to project root.

    For example, if code_path is /proj/pdd/crm_models.py and project_root is /proj,
    returns 'pdd.crm_models'.
    """
    try:
        relative = code_path.resolve().relative_to(project_root.resolve())
    except ValueError:
        # code_path is not relative to project_root — use stem only
        return code_path.stem

    # Convert path parts to dotted module path, stripping .py extension
    parts = list(relative.parts)
    if parts and parts[-1].endswith(".py"):
        parts[-1] = parts[-1][:-3]
    return ".".join(parts)


def build_one_session_prompt(
    basename: str,
    language: str,
    pdd_files: Dict[str, Path],
    project_root: Path,
    *,
    target_coverage: float = 90.0,
) -> str:
    """
    Build the mega-prompt for one-session sync.

    Reads the module prompt, preprocesses includes, reads generated code,
    and assembles the full instruction from the LLM template.

    Args:
        basename: Module basename (e.g., 'crm_models').
        language: Target language (e.g., 'python').
        pdd_files: Dict from get_pdd_file_paths with keys 'prompt', 'code', 'example', 'test'.
        project_root: Project root directory.
        target_coverage: Target test coverage percentage.

    Returns:
        Fully assembled prompt string.
    """
    # Read and preprocess the module prompt (resolve <include> tags)
    prompt_path = pdd_files["prompt"]
    prompt_content = prompt_path.read_text(encoding="utf-8")
    resolved_prompt_content = preprocess(
        prompt_content, recursive=True, double_curly_brackets=False
    )

    # Read current generated code (must exist)
    code_path = pdd_files["code"]
    code_content = code_path.read_text(encoding="utf-8")

    # Load the mega-prompt template
    template = load_prompt_template("one_session_agent_LLM")
    if template is None:
        raise FileNotFoundError(
            "Could not find prompt template 'one_session_agent_LLM'. "
            "Ensure prompts/one_session_agent_LLM.prompt exists."
        )

    # Progress file path for step-level reporting
    # Sanitize basename to avoid nested paths for subdirectory modules (e.g., core/cloud)
    safe_basename = basename.replace("/", "_")
    progress_file = project_root / f".pdd_one_session_progress_{safe_basename}"

    # Compute import base for example generation guidance
    import_base = _compute_import_base(code_path, project_root)

    # Step numbering is fixed: example=1, crash=2, verify=3, test=4
    verify_step_num = 3
    test_step_num = 4

    # Escape braces in dynamic content to prevent .format() from interpreting
    # code like {uid} or {name} as template placeholders
    def _escape_braces(s: str) -> str:
        return s.replace("{", "{{").replace("}", "}}")

    safe_prompt_content = _escape_braces(resolved_prompt_content)
    safe_code_content = _escape_braces(code_content)

    # Substitute all placeholders
    prompt = template.format(
        basename=basename,
        language=language,
        prompt_path=pdd_files["prompt"],
        code_path=pdd_files["code"],
        example_path=pdd_files["example"],
        test_path=pdd_files["test"],
        project_root=project_root,
        resolved_prompt_content=safe_prompt_content,
        code_content=safe_code_content,
        target_coverage=target_coverage,
        progress_file=progress_file,
        import_base=import_base,
        verify_step_num=verify_step_num,
        test_step_num=test_step_num,
    )

    return prompt


def run_one_session_sync(
    basename: str,
    language: str,
    pdd_files: Dict[str, Path],
    project_root: Path,
    *,
    target_coverage: float = 90.0,
    budget: Optional[float] = None,
    verbose: bool = False,
    quiet: bool = False,
    timeout: Optional[float] = None,
) -> Dict[str, Any]:
    """
    Run example/crash/verify/test/fix in a single agentic session.

    Args:
        basename: Module basename.
        language: Target language.
        pdd_files: Dict from get_pdd_file_paths.
        project_root: Project root directory.
        target_coverage: Target test coverage percentage.
        budget: Max cost budget (informational, not enforced here).
        verbose: Enable verbose output.
        quiet: Suppress output.
        timeout: Session timeout in seconds (default: 1200).

    Returns:
        Dict with keys: success, total_cost, model_name, operations_completed, errors.
    """
    # Validate code file exists (generated by prior pdd generate step)
    code_path = pdd_files["code"]
    if not code_path.exists():
        raise FileNotFoundError(
            f"Code file not found: {code_path}\n"
            f"Run `pdd generate {basename}` first."
        )
    prompt_path = pdd_files["prompt"]
    prompt_content = prompt_path.read_text(encoding="utf-8") if prompt_path.exists() else ""
    test_path = pdd_files.get("test")
    existing_test_content: Optional[str] = None
    if test_path and test_path.exists():
        try:
            existing_test_content = test_path.read_text(encoding="utf-8")
        except OSError:
            existing_test_content = None

    # Snapshot the pre-session code content (#1012, P1.A) so the
    # public-surface regression gate can run after the agentic session
    # rewrites the code file. Without this gate, `pdd sync --one-session`
    # (the default issue-sync path) bypasses the public-surface check
    # entirely — `sync_main.py:1093-1094` skips the in-process
    # `code_generator_main` call when the code file already exists and
    # hands off straight to `run_one_session_sync`, which previously
    # only verified test churn.
    existing_code_content: Optional[str] = None
    try:
        existing_code_content = code_path.read_text(encoding="utf-8")
    except OSError:
        existing_code_content = None

    # Pre-session snapshot of EVERY test-like file in the project so the
    # alt-path churn sweep below catches multi-file rewrites the
    # canonical-only check misses. Greg's review of PR #1015 surfaced
    # the false negative: the agent can rewrite a pre-existing
    # `__tests__/widget.test.ts` from 20 tests to 1 while leaving the
    # canonical `tests/widget.test.ts` untouched, and without this
    # snapshot the canonical churn check at line ~650 sees no change
    # and passes. The snapshot lives outside the retry loop because the
    # repair-loop restore writes back from these bytes — the snapshot
    # is the single source of truth for the pre-session baseline across
    # all attempts. `_snapshot_pre_test_contents` filters via
    # `_is_test_output_path` so only files matching test-file naming
    # conventions are captured.
    pre_test_contents: Dict[Path, str] = _snapshot_pre_test_contents(
        project_root, _get_file_mtimes(project_root).keys()
    )

    # Build the mega-prompt
    prompt = build_one_session_prompt(
        basename=basename,
        language=language,
        pdd_files=pdd_files,
        project_root=project_root,
        target_coverage=target_coverage,
    )

    logger.info("Starting one-session sync for %s (%s)", basename, language)

    # Progress file for step-level reporting from the agent
    # Sanitize basename to avoid nested paths for subdirectory modules (e.g., core/cloud)
    safe_basename = basename.replace("/", "_")
    progress_file = project_root / f".pdd_one_session_progress_{safe_basename}"
    # Clean up any stale progress file from a previous run
    if progress_file.exists():
        progress_file.unlink()

    # Show planned steps before starting
    if not quiet:
        rprint(
            f"[bold cyan]One-session sync:[/bold cyan] {basename} ({language})\n"
            f"[dim]Steps: example -> crash-fix -> verify -> test & fix[/dim]"
        )

    # Run the agentic task with a progress heartbeat
    session_timeout = timeout if timeout is not None else 1200.0
    start_time = time.time()

    # Heartbeat thread polls progress file and prints step-level updates
    stop_heartbeat = threading.Event()
    last_reported_line_count = 0

    def _heartbeat() -> None:
        """Poll progress file every 10s and print new step completions."""
        nonlocal last_reported_line_count
        while not stop_heartbeat.wait(10.0):
            elapsed = time.time() - start_time
            mins, secs = divmod(int(elapsed), 60)
            if quiet:
                continue

            # Check for new progress markers
            new_steps = _read_new_progress(progress_file, last_reported_line_count)
            if new_steps:
                for step_name in new_steps:
                    display = _format_step_display(step_name)
                    console.print(
                        f"  [green]{display}[/green] [dim]({mins}m{secs:02d}s)[/dim]"
                    )
                    phase = _STEP_TO_PHASE.get(step_name)
                    if phase:
                        print(f"PDD_PHASE: {phase}", flush=True)
                last_reported_line_count += len(new_steps)
            else:
                # No new steps — just show elapsed time every 30s
                if int(elapsed) > 0 and int(elapsed) % 30 == 0:
                    console.print(
                        f"[dim]  {basename}: running ({mins}m{secs:02d}s)...[/dim]"
                    )

    heartbeat_thread = threading.Thread(target=_heartbeat, daemon=True)
    heartbeat_thread.start()

    # ------------------------------------------------------------------
    # Test-churn repair loop (Codex review #1015 Finding 2).
    #
    # Mirror the `_run_test_op_with_churn_retry` contract from
    # `sync_orchestration.py`: when the one-session test step produces a
    # high-churn rewrite, restore the prior test file, set
    # `PDD_REPAIR_DIRECTIVE` from the exception's `repair_directive`, and
    # rerun the agentic session once (bounded by `MAX_CONFORMANCE_ATTEMPTS`,
    # capped at one extra attempt per the orchestration-side semantics).
    # On exhaustion, emit the structured `=== test churn threshold
    # exceeded ===` block to stderr exactly once and raise the last
    # exception with accumulated cost/model. The prior
    # `PDD_REPAIR_DIRECTIVE` is restored in `finally` (or popped if it
    # was unset originally) so the env does not leak across operations.
    # Inlined rather than extracted because:
    #   - The orchestration helper wraps `cmd_test_main` (Click-level
    #     tuple), this path wraps `run_agentic_task` + a separate
    #     `_verify_test_churn` post-check.
    #   - One-session also restores the test file on failure, which the
    #     orchestration helper does not.
    #   - One-session manages heartbeat thread lifecycle around the call.
    # ------------------------------------------------------------------
    from .agentic_sync_runner import (
        MAX_CONFORMANCE_ATTEMPTS,
        build_public_surface_hard_failure_from_error,
        build_test_churn_hard_failure_from_error,
    )

    success: bool = False
    output_text: str = ""
    cost: float = 0.0
    provider: str = "unknown"
    accumulated_cost: float = 0.0
    accumulated_provider: str = ""
    last_churn_exc: Optional[TestChurnError] = None
    churn_gate_passed = True  # True when the last accepted attempt has no churn failure.
    last_churn_signature: Optional[tuple] = None
    # Public-surface gate state (#1012, P1.A): parallel to churn state.
    # Tracks the last PublicSurfaceRegressionError so the helper can
    # emit the public-surface hard-failure block on exhaustion and
    # short-circuit on identical-signature retries (same pattern as
    # the test-churn gate).
    last_surface_exc: Optional[PublicSurfaceRegressionError] = None
    surface_gate_passed = True
    last_surface_signature: Optional[tuple] = None
    # Split retry budgets per gate (Codex review #1015 iter-1, Important 2).
    # Previously, a single ``max_churn_attempts = min(MAX_CONFORMANCE_ATTEMPTS,
    # _MAX_TEST_CHURN_ATTEMPTS)`` capped BOTH gates at ``_MAX_TEST_CHURN_ATTEMPTS``
    # (=2). That mis-applied the churn cap to public-surface repair, which
    # should get the same retry budget the generate path uses — ``MAX_CONFORMANCE_ATTEMPTS``.
    # The outer loop now runs for the union budget (``MAX_CONFORMANCE_ATTEMPTS``),
    # and each gate enforces its own counter:
    #   - ``surface_attempts_used`` caps at ``MAX_CONFORMANCE_ATTEMPTS`` (parity
    #     with the generate-op repair loop).
    #   - ``churn_attempts_used`` caps at ``_MAX_TEST_CHURN_ATTEMPTS`` (=2)
    #     because rewriting tests on repeated prompts rarely converges and
    #     just burns budget.
    # The identical-signature short-circuit and cost-budget checks fire per
    # gate as before. The outer loop budget is the larger of the two so a
    # surface failure that follows an earlier churn failure (or vice versa)
    # still has retry headroom; per-gate counters prevent either gate from
    # leaking attempts to the other.
    max_outer_attempts = max(MAX_CONFORMANCE_ATTEMPTS, _MAX_TEST_CHURN_ATTEMPTS)
    max_surface_attempts = MAX_CONFORMANCE_ATTEMPTS
    max_churn_attempts_for_churn = _MAX_TEST_CHURN_ATTEMPTS
    # Per-gate counters incremented when the gate actually FAILS (the loop
    # has not yet decided to retry). Each gate breaks the outer loop when
    # its own counter exhausts.
    surface_attempts_used = 0
    churn_attempts_used = 0

    prev_repair_directive = os.environ.get("PDD_REPAIR_DIRECTIVE")
    # Pop the env var BEFORE attempt 1 (#1012, F-I) so the subprocess
    # spawned by `run_agentic_task` AND any re-entrant PDD CLI process
    # the agent launches during attempt 1 inherit a CLEAN env. Without
    # this, a stale outer `PDD_REPAIR_DIRECTIVE` (set by the caller's
    # shell, a parent orchestration layer, or a prior PDD command) would
    # leak into the first subprocess and any nested `pdd test`/
    # `pdd generate` invocations the agent runs as tool calls would
    # append the stale directive to their own prompts. Mirrors the
    # parallel fix in `sync_orchestration._run_test_op_with_churn_retry`.
    # The `finally` block below restores the prior outer value when the
    # loop exits.
    os.environ.pop("PDD_REPAIR_DIRECTIVE", None)
    # Loop-local directive for instruction rewrite (#1012, F-E followup
    # iter-9). We deliberately do NOT read `PDD_REPAIR_DIRECTIVE` from
    # the environment when building `instruction_for_attempt`: a stale
    # outer value would otherwise contaminate attempt 1's instruction
    # even though no one-session churn failure has occurred yet. Only
    # `TestChurnError` raised inside THIS loop populates this variable.
    # The env-var write below (set AFTER catching a churn error and
    # before the retry) is still performed because children spawned by
    # `run_agentic_task` inherit the parent env and a re-entrant PDD
    # CLI process reads the env var to build its own repair directive;
    # but the local variable is the source of truth for THIS loop's
    # instruction rewrite.
    pending_repair_directive: Optional[str] = None
    try:
        for churn_attempt in range(max_outer_attempts):
            # Per-attempt instruction: `run_agentic_task` does NOT read
            # `PDD_REPAIR_DIRECTIVE` itself, so we must append the
            # directive to the instruction string ourselves for the
            # retry. Without this, the second attempt sees the
            # IDENTICAL prompt as the first and the repair loop cannot
            # actually repair. The base `prompt` stays intact so
            # downstream parsers see a stable shape across attempts.
            # First attempt: pending_repair_directive is None (loop just
            # started), so the instruction equals the base prompt.
            if pending_repair_directive and pending_repair_directive.strip():
                instruction_for_attempt = (
                    f"{prompt}\n\n<test_repair_directive>\n"
                    f"{pending_repair_directive.strip()}\n"
                    "</test_repair_directive>\n"
                )
            else:
                instruction_for_attempt = prompt
            try:
                success, output_text, cost, provider = run_agentic_task(
                    instruction=instruction_for_attempt,
                    cwd=project_root,
                    verbose=verbose,
                    quiet=quiet,
                    label=f"one_session_sync:{basename}",
                    timeout=session_timeout,
                    # One-session runs deploy with anthropic-only in cloud (no fallback
                    # provider). Pass max_retries=2 so the false-positive single-provider
                    # retry path actually fires — without this, the default of 1 means
                    # one transient empty response from Claude Code fails the whole sync.
                    max_retries=2,
                )
            finally:
                # Heartbeat lifecycle: stop the running thread for this attempt
                # so post-run drain / clean-up can proceed. On a retry we will
                # start a fresh heartbeat thread.
                stop_heartbeat.set()
                heartbeat_thread.join(timeout=2.0)

                # Print any remaining progress that arrived after last heartbeat
                if not quiet:
                    remaining = _read_new_progress(progress_file, last_reported_line_count)
                    elapsed = time.time() - start_time
                    mins, secs = divmod(int(elapsed), 60)
                    for step_name in remaining:
                        display = _format_step_display(step_name)
                        console.print(
                            f"  [green]{display}[/green] [dim]({mins}m{secs:02d}s)[/dim]"
                        )
                        phase = _STEP_TO_PHASE.get(step_name)
                        if phase:
                            print(f"PDD_PHASE: {phase}", flush=True)

                # Clean up progress file
                if progress_file.exists():
                    try:
                        progress_file.unlink()
                    except OSError:
                        pass

            # Accumulate cost/model across attempts so failed attempts are
            # still charged. On the final raise the exception carries the
            # total cost; on a successful retry the caller's returned
            # `total_cost` includes prior failed attempts (mirrors the
            # generate-op accumulation in `sync_orchestration.py`).
            attempt_cost = float(cost or 0.0)
            accumulated_cost += attempt_cost
            if provider and provider != "unknown":
                accumulated_provider = provider

            # Only run gates when the session reported success.
            if not success:
                churn_gate_passed = True
                surface_gate_passed = True
                break

            # Optimistically reset gate-passed flags for THIS attempt.
            # If either gate raises below, the except handlers set
            # ``*_gate_passed = False`` and the post-loop logic emits
            # the appropriate hard-failure block. Without this reset,
            # a previously-failed gate that PASSES on the retry would
            # still appear failed at function exit because the loop
            # variable wasn't refreshed.
            surface_gate_passed = True
            churn_gate_passed = True

            # Public-surface regression gate (#1012, P1.A): runs FIRST
            # because an API break is higher-priority than a test
            # rewrite. The agent rewrites the code file directly, so
            # we re-read it from disk (not from the agent's
            # `output_text`) and pass to `_verify_public_surface_regression`
            # with the pre-session snapshot. The except handler below
            # restores the pre-session code file from
            # `existing_code_content` and routes through the same
            # repair-loop retry pattern as the test-churn gate.
            try:
                if existing_code_content and existing_code_content.strip():
                    try:
                        generated_code_content = code_path.read_text(encoding="utf-8")
                    except OSError:
                        generated_code_content = ""
                    _verify_public_surface_regression(
                        existing_code=existing_code_content,
                        generated_code=generated_code_content,
                        prompt_name=f"{basename}_{language}.prompt",
                        output_path=str(code_path),
                        language=language,
                        prompt_content=prompt_content,
                    )
            except PublicSurfaceRegressionError as surface_err:
                # Restore the pre-session code file before deciding on
                # retry so the agent's broken code does NOT persist on
                # disk between attempts.
                try:
                    code_path.write_text(existing_code_content or "", encoding="utf-8")
                except OSError:
                    pass
                # P2.B / P3.B: also restore the pre-session test file
                # when the surface gate fires. The agent rewrites the
                # test file as part of the one-session run, and surface
                # failures `continue` before the test-churn gate runs
                # — so a deleted/high-churn test file from the failed
                # attempt would otherwise remain on disk even if the
                # surface error is what ultimately surfaces.
                # Restoration here keeps disk state clean regardless of
                # whether surface or churn ends up being the
                # user-facing diagnostic. Use ``is not None`` (not
                # truthiness) so an empty pre-session test file is also
                # restored to its zero-byte state instead of being left
                # in whatever state the agent put it in.
                if test_path is not None and existing_test_content is not None:
                    try:
                        test_path.parent.mkdir(parents=True, exist_ok=True)
                        test_path.write_text(existing_test_content, encoding="utf-8")
                    except OSError:
                        pass
                # iter-17 (Greg iter-16 follow-up review): restore EVERY
                # alt-path test-like file from the pre-session snapshot
                # too. Without this, a one-session attempt that both
                # regresses public surface AND rewrites/deletes an alt-
                # path test file (e.g. removes `keep_me()` while deleting
                # `src/widget_test.py`) would surface the
                # PublicSurfaceRegressionError, restore code + canonical,
                # but leave the alt-path damage on disk — silently
                # discarding broad existing coverage as a side effect of
                # a higher-priority surface failure. Mirrors the
                # churn-handler restoration loop below. The canonical
                # was already restored above; skip it here.
                for snap_path, snap_content in pre_test_contents.items():
                    if test_path is not None:
                        try:
                            if snap_path.samefile(test_path):
                                continue
                        except OSError:
                            try:
                                if snap_path.resolve() == test_path.resolve():
                                    continue
                            except OSError:
                                pass
                    try:
                        snap_path.parent.mkdir(parents=True, exist_ok=True)
                        snap_path.write_text(snap_content, encoding="utf-8")
                    except OSError:
                        pass
                signature = (
                    tuple(sorted(set(surface_err.removed_symbols))),
                    tuple(sorted(set(getattr(surface_err, "changed_signatures", []) or []))),
                )
                last_surface_exc = surface_err
                surface_gate_passed = False
                churn_gate_passed = True  # Surface failure overrides — churn not evaluated.
                surface_attempts_used += 1
                # Identical-signature short-circuit (mirror the
                # churn-gate behavior).
                if (
                    last_surface_signature is not None
                    and signature == last_surface_signature
                ):
                    break
                last_surface_signature = signature
                # Public-surface repair gets the FULL ``MAX_CONFORMANCE_ATTEMPTS``
                # budget (#1015 iter-1, Important 2) — independent of the
                # churn cap. Stop when this gate's per-counter is exhausted.
                if surface_attempts_used >= max_surface_attempts:
                    break
                # Record the directive for the next attempt's
                # instruction rewrite and set the env var so any
                # re-entrant PDD CLI process spawned by
                # `run_agentic_task` (inheriting the parent env) can
                # read it. Rebuild the heartbeat thread.
                pending_repair_directive = surface_err.repair_directive
                os.environ["PDD_REPAIR_DIRECTIVE"] = surface_err.repair_directive
                last_reported_line_count = 0
                if progress_file.exists():
                    try:
                        progress_file.unlink()
                    except OSError:
                        pass
                stop_heartbeat = threading.Event()
                heartbeat_thread = threading.Thread(target=_heartbeat, daemon=True)
                heartbeat_thread.start()
                continue  # Skip the churn gate this attempt; retry the session.

            # Skip both the canonical churn check AND the alt-path
            # sweep when the operator has opted out of conformance
            # gates (#1012, F-K). Either `PDD_SKIP_TEST_CHURN_GATE=1`
            # (per-gate flag) or `PDD_SKIP_CONFORMANCE=1` (umbrella
            # flag) disables this check. The standard `_verify_test_churn`
            # also honors both flags internally, but the deletion-as-churn
            # shortcut below raises ``TestChurnError`` directly without
            # going through that helper, so it needs an explicit guard
            # here. The prompt-side `BREAKING-CHANGE: rewrite tests`
            # opt-out parsed by `_prompt_allows_test_churn` is honored
            # here too so a deletion is treated symmetrically with a
            # non-empty rewrite. Moved above the canonical-empty
            # early-return so the alt-path sweep also honors opt-outs.
            if (
                _env_flag_enabled("PDD_SKIP_TEST_CHURN_GATE")
                or _env_flag_enabled("PDD_SKIP_CONFORMANCE")
                or _prompt_allows_test_churn(prompt_content)
            ):
                churn_gate_passed = True
                break

            # Track whether canonical existed pre-session — the deletion-
            # as-churn shortcut and the canonical-only `_verify_test_churn`
            # call below both require a non-None baseline.
            canonical_existed = bool(test_path and existing_test_content)

            try:
                # Multi-file alt-path churn sweep. Walks every test-like
                # file captured in the pre-session snapshot and checks
                # both rewrites AND deletions against the snapshot.
                # Iter-15 introduced the rewrite sweep; iter-16 closes
                # the residual deletion false negative Greg flagged in
                # his follow-up review (an agent deleting a pre-existing
                # alt-path test file while leaving canonical intact
                # previously slipped past the gate because the sweep
                # `continue`d on missing files). First-time creations
                # are not in the snapshot and fall through (exempt by
                # design). The canonical path is skipped here so its
                # deletion-as-churn shortcut + repair directive below
                # remain canonical-specific.
                for snap_path, prior in pre_test_contents.items():
                    if not prior:
                        continue  # zero-byte pre-session file — nothing to protect
                    # Skip the canonical — dedicated check below.
                    if test_path is not None:
                        try:
                            if snap_path.samefile(test_path):
                                continue
                        except OSError:
                            try:
                                if snap_path.resolve() == test_path.resolve():
                                    continue
                            except OSError:
                                pass
                    # Deletion case: treat as maximal churn (ratio=1.0).
                    # Mirrors the canonical-deletion shortcut below so
                    # alt-path deletions are handled symmetrically.
                    if not snap_path.exists():
                        threshold = _get_test_churn_threshold()
                        pre_line_count = len(prior.splitlines())
                        raise TestChurnError(
                            prompt_name=f"{basename}_test_{language}.prompt",
                            output_path=str(snap_path),
                            churn_ratio=1.0,
                            threshold=threshold,
                            pre_line_count=pre_line_count,
                            post_line_count=0,
                            repair_directive=(
                                "Test churn repair required.\n"
                                f"- The pre-existing alternate test file at "
                                f"{snap_path} was DELETED by the agent.\n"
                                "- Recreate the file preserving the prior "
                                "test function names and coverage; do not "
                                "drop accumulated regression tests.\n"
                                "- Add new tests for the prompt change "
                                "without deleting pre-existing test files."
                            ),
                        )
                    # Rewrite case: file still exists, compare content.
                    try:
                        current = snap_path.read_text(encoding="utf-8")
                    except OSError:
                        continue
                    if current == prior:
                        continue
                    _verify_test_churn(
                        existing_code=prior,
                        generated_code=current,
                        prompt_name=f"{basename}_test_{language}.prompt",
                        output_path=str(snap_path),
                        prompt_content=prompt_content,
                    )

                # Canonical churn check (only when a baseline exists).
                # A deleted canonical test file is the most extreme
                # form of coverage loss — treat it as maximal churn
                # (ratio=1.0) so the same repair-loop retry that
                # handles wholesale rewrites also handles deletions.
                # The except handler below restores the pre-existing
                # content from `existing_test_content`.
                if canonical_existed:
                    if not test_path.exists():
                        threshold = _get_test_churn_threshold()
                        pre_line_count = len(existing_test_content.splitlines())
                        raise TestChurnError(
                            prompt_name=f"{basename}_test_{language}.prompt",
                            output_path=str(test_path),
                            churn_ratio=1.0,
                            threshold=threshold,
                            pre_line_count=pre_line_count,
                            post_line_count=0,
                            repair_directive=(
                                "Test churn repair required.\n"
                                f"- The regenerated test file was DELETED from {test_path}.\n"
                                "- Rewrite the test file preserving the prior test "
                                "function names and coverage; do not omit accumulated "
                                "regression tests.\n"
                                "- Add new tests for the prompt change without removing "
                                "the pre-existing ones."
                            ),
                        )
                    generated_test_content = test_path.read_text(encoding="utf-8")
                    _verify_test_churn(
                        existing_code=existing_test_content,
                        generated_code=generated_test_content,
                        prompt_name=f"{basename}_test_{language}.prompt",
                        output_path=str(test_path),
                        prompt_content=prompt_content,
                    )
                # Gate passed — accept this attempt.
                churn_gate_passed = True
                break
            except TestChurnError as churn_err:
                # Restore the pre-session code file BEFORE the retry/break
                # decision. The agentic session rewrites both code and test
                # in-place; rejecting only the test would leave the code
                # mutated on disk, so the next ``pdd sync`` would treat the
                # mutated code as the baseline. Mirror the surface handler
                # at lines ~530-533: best-effort write, swallow ``OSError``.
                # ``existing_code_content`` is captured once pre-loop at
                # line ~248-252 (the same bytes the surface gate compares
                # against), so restoring to those bytes keeps subsequent
                # invocations seeing a clean baseline.
                if existing_code_content is not None:
                    try:
                        code_path.write_text(
                            existing_code_content, encoding="utf-8"
                        )
                    except OSError:
                        pass
                # Restore the canonical test file when one existed
                # pre-session. (When canonical didn't exist, restoring
                # is a no-op and `existing_test_content` is None.)
                if canonical_existed:
                    test_path.write_text(existing_test_content, encoding="utf-8")
                # Restore EVERY alt-path snapshot so the next attempt's
                # re-snapshot sees the true pre-session state. Covers
                # both rewrites (overwrite back to pre-session bytes)
                # AND deletions (recreate the file, plus any directories
                # the agent removed along with it). Without this,
                # attempt N's surviving rewrites become attempt N+1's
                # baseline and the gate permanently weakens. The
                # canonical was already restored above; skip it here.
                for snap_path, snap_content in pre_test_contents.items():
                    if test_path is not None:
                        try:
                            if snap_path.samefile(test_path):
                                continue
                        except OSError:
                            try:
                                if snap_path.resolve() == test_path.resolve():
                                    continue
                            except OSError:
                                pass
                    try:
                        snap_path.parent.mkdir(parents=True, exist_ok=True)
                        snap_path.write_text(snap_content, encoding="utf-8")
                    except OSError:
                        pass
                signature = (
                    f"{churn_err.churn_ratio:.2f}",
                    str(churn_err.pre_line_count),
                )
                last_churn_exc = churn_err
                churn_gate_passed = False
                churn_attempts_used += 1
                # Stop early when the retry produced the identical churn
                # signature (no progress is being made) — mirrors the
                # orchestration helper's short-circuit.
                if (
                    last_churn_signature is not None
                    and signature == last_churn_signature
                ):
                    break
                last_churn_signature = signature
                # Test-churn keeps its tighter ``_MAX_TEST_CHURN_ATTEMPTS`` cap
                # (#1015 iter-1, Important 2). Surface repair uses a separate
                # counter so a single surface failure cannot eat the churn
                # budget and vice versa.
                if churn_attempts_used >= max_churn_attempts_for_churn:
                    break
                # Record the directive for the next attempt's instruction
                # rewrite (loop-local source of truth) AND set the env var
                # so any re-entrant PDD CLI process spawned by
                # `run_agentic_task` (which inherits the parent env) can
                # read it. Rebuild the heartbeat thread so the next session
                # can report step-level progress.
                pending_repair_directive = churn_err.repair_directive
                os.environ["PDD_REPAIR_DIRECTIVE"] = churn_err.repair_directive
                last_reported_line_count = 0
                if progress_file.exists():
                    try:
                        progress_file.unlink()
                    except OSError:
                        pass
                stop_heartbeat = threading.Event()
                heartbeat_thread = threading.Thread(target=_heartbeat, daemon=True)
                heartbeat_thread.start()
    finally:
        if prev_repair_directive is None:
            os.environ.pop("PDD_REPAIR_DIRECTIVE", None)
        else:
            os.environ["PDD_REPAIR_DIRECTIVE"] = prev_repair_directive

    elapsed = time.time() - start_time
    mins, secs = divmod(int(elapsed), 60)

    # Emit final phase marker for runner to parse
    if success and churn_gate_passed and surface_gate_passed:
        print("PDD_PHASE: synced", flush=True)
    else:
        print("PDD_PHASE: conflict", flush=True)

    # Show completion summary using accumulated cost so failed attempts are
    # visible in the user-facing status line.
    if not quiet:
        status = (
            "[green]Success[/green]"
            if success and churn_gate_passed and surface_gate_passed
            else "[red]Failed[/red]"
        )
        rprint(
            f"[bold]One-session sync {status}[/bold] "
            f"({mins}m{secs:02d}s, ${accumulated_cost:.4f})"
        )

    # If the public-surface gate never accepted across all attempts,
    # emit the structured hard-failure block to stderr exactly once and
    # raise the last exception with the accumulated cost/model attached.
    # Public-surface regression takes priority over test churn because
    # an API break is higher-impact for downstream callers. The two
    # gates can never both leave behind a "failed" state on the same
    # attempt — surface failures `continue` before the churn gate runs
    # — so only one of these blocks can fire per `run_one_session_sync`
    # call.
    if last_surface_exc is not None and not surface_gate_passed:
        last_surface_exc.total_cost = float(accumulated_cost or 0.0)
        last_surface_exc.model_name = accumulated_provider or provider or "unknown"
        hard_block = build_public_surface_hard_failure_from_error(
            last_surface_exc, basename
        )
        print(hard_block, file=sys.stderr)
        raise last_surface_exc

    # If the churn gate never accepted across all attempts, emit the
    # structured hard-failure block to stderr exactly once and raise the
    # last exception with the accumulated cost/model attached.
    if last_churn_exc is not None and not churn_gate_passed:
        last_churn_exc.total_cost = float(accumulated_cost or 0.0)
        last_churn_exc.model_name = accumulated_provider or provider or "unknown"
        hard_block = build_test_churn_hard_failure_from_error(last_churn_exc, basename)
        print(hard_block, file=sys.stderr)
        raise last_churn_exc

    # Determine which operations were completed
    operations: List[str] = []
    if success:
        operations = ["example", "crash_fix", "verify", "test"]

    errors: List[str] = []
    if not success:
        errors.append(output_text[:500] if output_text else "One-session sync failed")

    return {
        "success": success,
        # Use accumulated cost so failed-then-retried attempts charge the
        # operator for every agentic session run (mirrors the generate-op
        # cost accumulation in `sync_orchestration.py`).
        "total_cost": float(accumulated_cost or cost or 0.0),
        "model_name": accumulated_provider or provider,
        "operations_completed": operations,
        "errors": errors,
        # sync_main's summary table reads result.get("error") (singular).
        # Without this key, one-session errors display as "No details."
        "error": "; ".join(errors) if errors else "",
    }
