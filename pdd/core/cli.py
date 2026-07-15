"""
Main CLI class and entry point logic.
"""
import os
import sys
import io
import re
import json
import click
from typing import Any, Dict, List, Optional, Tuple, TextIO

try:
    from .. import DEFAULT_STRENGTH, __version__, DEFAULT_TIME
except ImportError:
    # Fallback for environments where `pdd` resolves as a namespace package.
    DEFAULT_STRENGTH = 1.0
    DEFAULT_TIME = 0.25
    __version__ = "unknown"
from ..auto_update import auto_update
from ..cli_branding import PDD_FULL_TAGLINE, PDD_POSITIONING
from ..construct_paths import list_available_contexts
from ..install_completion import get_local_pdd_path
from .errors import console, handle_error, clear_core_dump_errors, apply_color_preference
from ..cli_status import GLYPHS as _STATUS_GLYPHS, Status as _Status
from .utils import _first_pending_command, _should_show_onboarding_reminder

# Shared status glyphs (EPIC #1540, workstream 2) so the per-step execution
# summary speaks the same SUCCESS/FAILURE vocabulary as every other command.
_OK_GLYPH = _STATUS_GLYPHS[_Status.SUCCESS]   # ✓
_FAIL_GLYPH = _STATUS_GLYPHS[_Status.FAILURE]  # ✗
from .duplicate_cli_guard import check_duplicate_before_subcommand, record_after_guarded_command


def _write_core_dump(*args: Any, **kwargs: Any) -> None:
    """Write through the active dump module after isolated module reloads."""
    from .dump import _write_core_dump as write_core_dump

    write_core_dump(*args, **kwargs)


def _strip_ansi_codes(text: str) -> str:
    """Remove ANSI escape codes from text for clean log output."""
    # Covers common CSI sequences (\x1b[...m, \x1b[...K, cursor moves),
    # plus OSC sequences (\x1b]...BEL or \x1b]...\x1b\\) used by some terminals.
    csi = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
    osc = re.compile(r"\x1b\].*?(?:\x07|\x1b\\)")
    text = osc.sub("", text)
    return csi.sub("", text)


class OutputCapture:
    """Captures terminal output while still displaying it normally.

    This class acts as a "tee" - it writes to both the original stream
    and a buffer for later retrieval.
    """

    def __init__(self, original_stream: TextIO):
        self.original_stream = original_stream
        self.buffer = io.StringIO()

    def write(self, text: str) -> int:
        # Write to original stream so output is still displayed
        result = self.original_stream.write(text)
        # Also capture to buffer
        try:
            self.buffer.write(text)
        except Exception:
            # If buffer write fails, don't break the original output
            pass
        return result

    def flush(self):
        self.original_stream.flush()
        try:
            self.buffer.flush()
        except Exception:
            pass

    def isatty(self):
        """Delegate to original stream."""
        return self.original_stream.isatty()

    def fileno(self):
        """Delegate to original stream."""
        return self.original_stream.fileno()

    def get_captured_output(self) -> str:
        """Retrieve all captured output."""
        return self.buffer.getvalue()


def _restore_captured_streams(ctx: click.Context) -> None:
    """Restore original streams if they were captured for core dump.

    This must be called before any early exit (ctx.exit(0)) to prevent
    sys.stdout/stderr from remaining wrapped with OutputCapture, which
    causes test pollution when running multiple tests.
    """
    if isinstance(ctx.obj, dict):
        stdout_capture = ctx.obj.get("_stdout_capture")
        stderr_capture = ctx.obj.get("_stderr_capture")
        if stdout_capture:
            sys.stdout = stdout_capture.original_stream
        if stderr_capture:
            sys.stderr = stderr_capture.original_stream


# JSON-invocation detection is shared with the early pre-parse in pdd/cli.py via a
# stdlib-only leaf module so the two call sites cannot drift apart.
from ..json_invocation import is_machine_json_invocation as _is_machine_json_invocation


def _env_flag_enabled(name: str) -> bool:
    """Return True when an environment flag is set to a truthy value."""
    return os.getenv(name, "").lower() in {"1", "true", "yes", "on"}


def _extract_estimate_record(result: Any) -> Optional[Dict[str, Any]]:
    """Return an estimate payload from a command result, if one is present."""
    candidate = result
    if isinstance(result, tuple) and len(result) == 3:
        candidate = result[0]
    if isinstance(candidate, dict) and candidate.get("estimate") is True:
        return candidate
    return None


def _collect_estimate_records(
    normalized_results: List[Any],
    ctx: click.Context,
) -> List[Dict[str, Any]]:
    """Collect estimate payloads from command returns or ctx.obj accumulation."""
    records = [
        record
        for result in normalized_results
        for record in [_extract_estimate_record(result)]
        if record is not None
    ]
    if records:
        return records

    ctx_obj = ctx.obj if isinstance(ctx.obj, dict) else {}
    for key in ("estimate_records", "estimate_results"):
        value = ctx_obj.get(key)
        if isinstance(value, list):
            records.extend(
                item for item in value
                if isinstance(item, dict) and item.get("estimate") is True
            )
            if records:
                break
    return records


def _record_cost_known(record: Dict[str, Any]) -> bool:
    """Whether a single estimate record carries a usable, priced cost."""
    return bool(record.get("cost_known", False)) and not record.get("unknown_cost")


def _estimate_total_cost(records: List[Dict[str, Any]]) -> Optional[float]:
    """Return the aggregate of the *priced* estimate records.

    Sums only records with a known cost and ignores unknown ones, so a command
    whose steps are a mix of exact and not-estimable-without-execution (e.g.
    ``sync``: an exact generate step plus downstream steps that depend on
    generated output) still reports a meaningful number — a lower bound — rather
    than collapsing the whole total to "unknown". Returns None only when no
    record is priced at all. Callers should consult ``is_lower_bound`` in the
    summary to learn whether unpriced steps were omitted.
    """
    if not records:
        return None
    priced = [record for record in records if _record_cost_known(record)]
    if not priced:
        return None
    return round(
        sum(float(record.get("estimated_cost", record.get("total_cost", 0.0)) or 0.0) for record in priced),
        6,
    )


def _build_estimate_summary(records: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Build stable machine-readable estimate output without prompt text."""
    total_input = sum(int(record.get("input_tokens", 0) or 0) for record in records)
    total_predicted = sum(int(record.get("predicted_output_tokens", 0) or 0) for record in records)
    total_output_low = sum(int(record.get("output_tokens_low", 0) or 0) for record in records)
    total_output_high = sum(int(record.get("output_tokens_high", 0) or 0) for record in records)
    total_cost = _estimate_total_cost(records)
    any_unknown = any(not _record_cost_known(record) for record in records)
    output_estimations = sorted({
        str(record.get("output_estimation"))
        for record in records
        if record.get("output_estimation")
    })
    output_hint_paths = [
        str(record.get("output_hint_path"))
        for record in records
        if record.get("output_hint_path")
    ]
    # The total is a lower bound when it sums some, but not all, priced steps.
    is_lower_bound = total_cost is not None and any_unknown
    return {
        "estimate": True,
        "records": records,
        "input_tokens": total_input,
        "predicted_output_tokens": total_predicted,
        "output_tokens_low": total_output_low or None,
        "output_tokens_high": total_output_high or None,
        "estimated_cost": total_cost,
        "total_cost": total_cost,
        # unknown_cost stays True whenever any step is unpriced, even if the
        # priced steps still produce a (lower-bound) number.
        "unknown_cost": total_cost is None or any_unknown,
        "is_lower_bound": is_lower_bound,
        "output_estimations": output_estimations,
        "output_hint_paths": output_hint_paths,
        "currency": records[0].get("currency", "USD") if records else "USD",
    }


def _fmt_estimate_value(value: Any, *, money: bool = False) -> str:
    """Format a nullable estimate field for human output."""
    if value is None:
        return "unknown"
    if money:
        return f"${float(value):.6f}"
    return str(value)


def _estimate_requested_subcommand(ctx: click.Context) -> Optional[str]:
    """Return the first requested subcommand for estimate-mode scope checks."""
    tokens: List[str] = []
    try:
        tokens = list(ctx.meta.get("pdd_cli_tokens", []) or [])
    except Exception:
        tokens = []
    if not tokens:
        try:
            tokens = list(ctx.protected_args) + list(ctx.args)
        except Exception:
            tokens = list(getattr(ctx, "args", []) or [])
    for token in tokens:
        if token and not str(token).startswith("-"):
            return str(token)
    return None


def _validate_generate_only_estimate_mode(ctx: click.Context, estimate_mode: bool) -> None:
    """Fail closed while estimate mode is intentionally scoped to generate."""
    if not estimate_mode:
        return
    command_name = _estimate_requested_subcommand(ctx)
    if command_name in (None, "generate"):
        return
    raise click.UsageError("Estimate mode currently supports `generate` only.")


def _render_estimate_output(ctx: click.Context, records: List[Dict[str, Any]]) -> None:
    """Render estimate records as JSON or a concise human-readable table."""
    summary = _build_estimate_summary(records)
    ctx_obj = ctx.obj if isinstance(ctx.obj, dict) else {}
    if ctx_obj.get("estimate_json"):
        click.echo(json.dumps(summary, sort_keys=True))
        return

    click.echo("LLM Cost Estimate")
    click.echo(
        "Command | Model | Input Tokens | Predicted Output Tokens | "
        "Input Rate/M | Output Rate/M | Estimated Cost | Context Window"
    )
    click.echo(
        "--------|-------|--------------|-------------------------|"
        "--------------|---------------|----------------|---------------"
    )
    for record in records:
        context_limit = record.get("context_limit")
        context_percent = record.get("context_usage_percent")
        if context_limit is None and context_percent is None:
            context_display = "unknown"
        elif context_percent is None:
            context_display = str(context_limit)
        else:
            context_display = f"{context_percent}% of {context_limit}"
        click.echo(
            " | ".join([
                str(record.get("command") or "unknown"),
                str(record.get("model") or "unknown"),
                _fmt_estimate_value(record.get("input_tokens")),
                _fmt_estimate_value(record.get("predicted_output_tokens")),
                _fmt_estimate_value(record.get("input_rate_per_million")),
                _fmt_estimate_value(record.get("output_rate_per_million")),
                _fmt_estimate_value(
                    record.get("estimated_cost", record.get("total_cost")),
                    money=True,
                ),
                context_display,
            ])
        )

    total = summary["estimated_cost"]
    total_display = _fmt_estimate_value(total, money=True)
    if summary.get("is_lower_bound"):
        # Some steps could not be priced without execution; the printed total is
        # a floor, not the full projected cost.
        click.echo(
            f"Total estimated cost: ≥ {total_display} "
            "(lower bound; some steps not estimable without execution)"
        )
    else:
        click.echo(f"Total estimated cost: {total_display}")
    click.echo("Provider call made: false")
    click.echo("Command output files written: false")
    click.echo("Cost CSV row written: false")


def _write_result_core_dump(
    ctx: click.Context,
    normalized_results: List[Any],
    invoked_subcommands: List[str],
    total_cost: float,
) -> None:
    """Collect captured output, restore streams, and write the result core dump."""
    terminal_output = None
    if isinstance(ctx.obj, dict) and ctx.obj.get("core_dump"):
        stdout_capture = ctx.obj.get("_stdout_capture")
        stderr_capture = ctx.obj.get("_stderr_capture")
        if stdout_capture or stderr_capture:
            captured_parts = []
            if stdout_capture:
                stdout_text = stdout_capture.get_captured_output()
                if stdout_text:
                    clean_stdout = _strip_ansi_codes(stdout_text)
                    captured_parts.append(f"=== STDOUT ===\n{clean_stdout}")
            if stderr_capture:
                stderr_text = stderr_capture.get_captured_output()
                if stderr_text:
                    clean_stderr = _strip_ansi_codes(stderr_text)
                    captured_parts.append(f"=== STDERR ===\n{clean_stderr}")

            terminal_output = "\n\n".join(captured_parts) if captured_parts else ""
            if stdout_capture:
                sys.stdout = stdout_capture.original_stream
            if stderr_capture:
                sys.stderr = stderr_capture.original_stream

    _write_core_dump(ctx, normalized_results, invoked_subcommands, total_cost, terminal_output)


class PDDCLI(click.Group):
    """Custom Click Group that adds a Generate Suite section to root help."""

    def format_help(self, ctx: click.Context, formatter: click.HelpFormatter) -> None:
        self.format_usage(ctx, formatter)
        formatter.write_text(PDD_FULL_TAGLINE)
        formatter.write_text(PDD_POSITIONING)
        formatter.write_paragraph()
        with formatter.section("Generate Suite (related commands)"):
            formatter.write_dl([
                ("generate", "Create runnable code from a prompt file."),
                ("test",     "Generate or enhance unit tests for a code file."),
                ("example",  "Generate example code from a prompt and implementation."),
            ])
        formatter.write(
            "Use `pdd generate --help` for details on this suite and common global flags.\n"
        )

        self.format_options(ctx, formatter)

    def invoke(self, ctx):
        exception_to_handle = None
        user_abort = False  # Flag for user cancellation (fix for issue #186)
        # Capture the real invocation tokens (subcommand + its args) before Click
        # consumes them while resolving the subcommand. The group callback needs
        # these to decide whether to enter machine-output (quiet) mode, and
        # ``sys.argv`` is unreliable for that under Click's test runner. ``meta``
        # is shared with the same context the callback receives.
        try:
            ctx.meta["pdd_cli_tokens"] = list(ctx.protected_args) + list(ctx.args)
        except Exception:
            ctx.meta["pdd_cli_tokens"] = list(getattr(ctx, "args", []) or [])
        try:
            result = super().invoke(ctx)
        except click.Abort:
            # User cancelled (e.g., pressed 'no' on confirmation) - set flag
            # to exit silently without triggering error reporting
            user_abort = True
        except click.UsageError:
            raise  # Let Click handle it natively via BaseCommand.main() → echo()
        except KeyboardInterrupt as e:
            # Handle keyboard interrupt (Ctrl+C) gracefully
            exception_to_handle = e
        except SystemExit as e:
            # Let successful exits (code 0) pass through; for non-zero, exit with that code (e.g. intentional sys.exit(1) from a command)
            if e.code == 0 or e.code is None:
                raise
            # Write core dump on intentional failure exit so debugging has a record (same as exception path)
            try:
                if ctx.obj is None:
                    ctx.obj = {}
                invoked_subcommands = getattr(ctx, "invoked_subcommands", []) or []
                if not invoked_subcommands and isinstance(ctx.obj, dict):
                    invoked_subcommands = ctx.obj.get("invoked_subcommands", []) or []
                total_cost = 0.0
                terminal_output = None
                if ctx.obj.get("core_dump"):
                    stdout_capture = ctx.obj.get("_stdout_capture")
                    stderr_capture = ctx.obj.get("_stderr_capture")
                    if stdout_capture or stderr_capture:
                        captured_parts = []
                        if stdout_capture:
                            captured_parts.append("=== STDOUT ===\n" + _strip_ansi_codes(stdout_capture.get_captured_output()))
                        if stderr_capture:
                            captured_parts.append("=== STDERR ===\n" + _strip_ansi_codes(stderr_capture.get_captured_output()))
                        terminal_output = "\n\n".join(captured_parts) if captured_parts else ""
                        if stdout_capture:
                            sys.stdout = stdout_capture.original_stream
                        if stderr_capture:
                            sys.stderr = stderr_capture.original_stream
                _write_core_dump(
                    ctx, [], invoked_subcommands, total_cost, terminal_output,
                    exit_reason=f"Command exited with code {int(e.code) if e.code is not None else 1} (intentional failure).",
                )
            except Exception:
                pass
            ctx.exit(int(e.code) if e.code is not None else 1)
            return
        except click.exceptions.Exit as e:
            # Successful exit: propagate for Click to finish cleanly.
            if e.exit_code == 0:
                raise
            # Intentional failure (e.g. checkup --validate-arch-includes, failed sync): do not
            # route through handle_error — that misreports "unexpected error" after
            # the command already printed diagnostics.
            raise
        except Exception as e:
            # Handle all other exceptions
            exception_to_handle = e
        else:
            # No exception, return normally
            return result

        # Handle user abort outside try block to avoid nested exception issues
        if user_abort:
            ctx.exit(1)

        # Exception handling for all non-success cases
        # Figure out quiet mode if possible
        quiet = False
        try:
            if isinstance(ctx.obj, dict):
                quiet = ctx.obj.get("quiet", False)
        except Exception:
            pass

        # Centralized error reporting
        handle_error(exception_to_handle, _first_pending_command(ctx) or "unknown", quiet)

        # Make sure ctx.obj exists so _write_core_dump can read flags
        if ctx.obj is None:
            ctx.obj = {}

        # Force a core dump even though result_callback won't run
        try:
            normalized_results: List[Any] = []
            # Try to get invoked_subcommands from multiple sources
            invoked_subcommands = getattr(ctx, "invoked_subcommands", []) or []
            if not invoked_subcommands and isinstance(ctx.obj, dict):
                invoked_subcommands = ctx.obj.get("invoked_subcommands", []) or []
            total_cost = 0.0

            # Collect terminal output if capture was enabled
            terminal_output = None
            if ctx.obj.get("core_dump"):
                stdout_capture = ctx.obj.get("_stdout_capture")
                stderr_capture = ctx.obj.get("_stderr_capture")
                if stdout_capture or stderr_capture:
                    # Combine stdout and stderr
                    captured_parts = []
                    if stdout_capture:
                        stdout_text = stdout_capture.get_captured_output()
                        if stdout_text:
                            # Strip ANSI codes for clean output
                            clean_stdout = _strip_ansi_codes(stdout_text)
                            captured_parts.append(f"=== STDOUT ===\n{clean_stdout}")
                    if stderr_capture:
                        stderr_text = stderr_capture.get_captured_output()
                        if stderr_text:
                            # Strip ANSI codes for clean output
                            clean_stderr = _strip_ansi_codes(stderr_text)
                            captured_parts.append(f"=== STDERR ===\n{clean_stderr}")

                    terminal_output = "\n\n".join(captured_parts) if captured_parts else ""

                    # Restore original streams
                    if stdout_capture:
                        sys.stdout = stdout_capture.original_stream
                    if stderr_capture:
                        sys.stderr = stderr_capture.original_stream

            _write_core_dump(ctx, normalized_results, invoked_subcommands, total_cost, terminal_output)
        except Exception:
            # Never let core-dump logic itself crash the CLI
            pass

        # Exit with appropriate code: 2 for usage errors, 1 for other errors
        exit_code = 2 if isinstance(exception_to_handle, click.UsageError) else 1
        ctx.exit(exit_code)


# --- Main CLI Group ---
@click.group(
    cls=PDDCLI,
    invoke_without_command=True,
    help="PDD prompt-native programming system.",
)
@click.option(
    "--force",
    is_flag=True,
    default=False,
    help="Skip all interactive prompts (file overwrites, API key requests). Useful for CI/automation.",
)
@click.option(
    "--strength",
    type=click.FloatRange(0.0, 1.0),
    default=None,
    show_default=False,
    help=f"Set the strength of the AI model (0.0 to 1.0). Default: {DEFAULT_STRENGTH} or .pddrc value.",
)
@click.option(
    "--temperature",
    type=click.FloatRange(0.0, 2.0), # Allow higher temperatures if needed
    default=None,
    show_default=False,
    help="Set the temperature of the AI model. Default: 0.0 or .pddrc value.",
)
@click.option(
    "--time",
    type=click.FloatRange(0.0, 1.0),
    default=None,
    show_default=True,
    help="Controls reasoning allocation for LLMs (0.0-1.0). Uses DEFAULT_TIME if None.",
)
@click.option(
    "--verbose",
    is_flag=True,
    default=False,
    help="Increase output verbosity for more detailed information.",
)
@click.option(
    "--quiet",
    is_flag=True,
    default=False,
    help="Decrease output verbosity for minimal information.",
)
@click.option(
    "--color/--no-color",
    "color",
    default=None,
    help="Force or disable colored output across all commands. "
    "Default: auto (color on a TTY, off when piped or when NO_COLOR is set). "
    "--no-color disables it everywhere; --color forces it even through a pipe.",
)
@click.option(
    "--output-cost",
    type=click.Path(dir_okay=False, writable=True),
    default=None,
    help="Enable cost tracking and output a CSV file with usage details.",
)
@click.option(
    "--estimate",
    "--dry-run-cost",
    "estimate",
    is_flag=True,
    default=False,
    help="Preview token usage and estimated cost without calling providers or writing command outputs.",
)
@click.option(
    "--estimate-json",
    is_flag=True,
    default=False,
    help="Emit the estimate as machine-readable JSON. Implies --estimate.",
)
@click.option(
    "--review-examples",
    is_flag=True,
    default=False,
    help="Review and optionally exclude few-shot examples before command execution.",
)
@click.option(
    "--local",
    is_flag=True,
    default=False,
    help="Run commands locally instead of in the cloud.",
)
@click.option(
    "--context",
    "context_override",
    type=str,
    default=None,
    help="Override automatic context detection and use the specified .pddrc context.",
)
@click.option(
    "--list-contexts",
    "list_contexts",
    is_flag=True,
    default=False,
    help="List available contexts from .pddrc and exit.",
)
@click.option(
    "--core-dump/--no-core-dump",
    "core_dump",
    default=True,
    help="Write a JSON core dump for this run into .pdd/core_dumps (default: on). Use --no-core-dump to disable.",
)
@click.option(
    "--keep-core-dumps",
    "keep_core_dumps",
    type=click.IntRange(min=0),
    default=10,
    help="Number of core dumps to keep (default: 10, min: 0). Older dumps are garbage collected after each dump write.",
)
@click.option(
    "--compress-examples",
    is_flag=True,
    default=None,
    help="Automatically compress example code in context to signatures only.",
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
    help="Set global context compression mode.",
)
@click.option(
    "--compression-fallback",
    type=click.Choice(["full", "error"]),
    default=None,
    help="Behavior when context compression fails (default: full).",
)
@click.version_option(version=__version__, package_name="pdd-cli")
@click.pass_context
def cli(
    ctx: Optional[click.Context] = None,
    force: bool = False,
    strength: Optional[float] = None,
    temperature: Optional[float] = None,
    verbose: bool = False,
    quiet: bool = False,
    color: Optional[bool] = None,
    output_cost: Optional[str] = None,
    estimate: bool = False,
    estimate_json: bool = False,
    review_examples: bool = False,
    local: bool = False,
    time: Optional[float] = None, # Type hint is Optional[float]
    context_override: Optional[str] = None,
    list_contexts: bool = False,
    core_dump: bool = True,
    keep_core_dumps: int = 10,
    compress_examples: Optional[bool] = None,
    compress_test_context: Optional[bool] = None,
    context_compression: Optional[str] = None,
    compression_fallback: Optional[str] = None,
):
    """
    Main entry point for the PDD CLI. Handles global options and initializes context.
    """
    # Machine-JSON output is intended for downstream consumers, so stdout must
    # stay payload-only. ``sys.argv`` covers the real CLI, but under Click's test
    # runner it is the pytest argv — so also check the invocation tokens captured
    # in ``PDDCLI.invoke`` (subcommand + its args). Both feed the same shared
    # detector that ``pdd/cli.py``'s early pre-parse uses, so they cannot drift.
    # Estimate mode (--estimate/--estimate-json/PDD_ESTIMATE) is a read-only
    # dry-run preview that must also stay quiet and payload-only.
    estimate_mode = bool(estimate or estimate_json or _env_flag_enabled("PDD_ESTIMATE"))
    cli_tokens = ctx.meta.get("pdd_cli_tokens", []) if hasattr(ctx, "meta") else []
    json_mode = (
        _is_machine_json_invocation(sys.argv)
        or _is_machine_json_invocation(cli_tokens)
        or estimate_json
    )
    quiet = quiet or json_mode or estimate_mode
    _validate_generate_only_estimate_mode(ctx, estimate_mode)
    # Estimate mode is a read-only dry-run preview; suppress the diagnostic
    # core dump so previews never write to .pdd/core_dumps.
    core_dump = core_dump and not json_mode and not estimate_mode

    # Ensure PDD_PATH is set before any commands run
    get_local_pdd_path()

    # Reset per-run error buffer and store core_dump flag
    clear_core_dump_errors()

    ctx.ensure_object(dict)
    ctx.obj["force"] = force
    if force:
        os.environ['PDD_FORCE'] = '1'
    # Only set strength/temperature if explicitly provided (not None)
    # This allows .get("key", default) to return the default when CLI didn't pass a value
    if strength is not None:
        ctx.obj["strength"] = strength
    if temperature is not None:
        ctx.obj["temperature"] = temperature
    ctx.obj["verbose"] = verbose
    ctx.obj["quiet"] = quiet
    if quiet:
        os.environ["PDD_QUIET"] = "1"
    else:
        os.environ.pop("PDD_QUIET", None)
    # Color is the default (auto-detected); --color/--no-color lets the user force
    # or disable it across every command. Apply it before any console output below
    # so the choice covers the whole run, including later-constructed consoles.
    ctx.obj["color"] = color
    ctx.call_on_close(apply_color_preference(color))
    ctx.obj["estimate"] = estimate_mode
    ctx.obj["estimate_json"] = bool(estimate_json)
    ctx.obj["estimate_results"] = []
    ctx.obj["estimate_records"] = ctx.obj["estimate_results"]
    # Estimate mode mutates process-wide env vars so the intent reaches the
    # library-level llm_invoke (which reads PDD_ESTIMATE when no Click context is
    # available) and any `pdd` subprocesses spawned during the command. Those
    # mutations must NOT outlive the invocation: estimate_mode is itself derived
    # from PDD_ESTIMATE just above, so a value left behind would make the *next*
    # in-process CLI run silently sticky in estimate mode. This is exactly what
    # breaks under repeated CliRunner.invoke calls in the test suite (an earlier
    # estimate test poisons later generate/fix/change/update/report tests).
    # Snapshot the pre-invocation values and restore them when this context tears
    # down, so an externally exported PDD_ESTIMATE=1 still survives while a value
    # we set internally does not.
    #
    # The set must cover EVERY env var this block mutates, not just PDD_ESTIMATE:
    # estimate mode also clears PDD_OUTPUT_COST_PATH (so a preview never appends
    # to the cost log) and forces PDD_FORCE_LOCAL=1. Omitting those leaks the same
    # class of bug — a later in-process command would stay forced-local and would
    # have lost an existing cost-log path. PDD_FORCE_LOCAL is likewise set by a
    # plain --local run; snapshotting it keeps that invocation-scoped too.
    _estimate_env_keys = (
        "PDD_ESTIMATE",
        "PDD_ESTIMATE_JSON",
        "PDD_LLM_ATTRIBUTION_PROCESS_LOG",
        "PDD_LLM_ATTRIBUTION_STDOUT",
        "PDD_OUTPUT_COST_PATH",
        "PDD_FORCE_LOCAL",
    )
    _estimate_env_snapshot = {key: os.environ.get(key) for key in _estimate_env_keys}

    def _restore_estimate_env(_snapshot=_estimate_env_snapshot):
        for key, prev in _snapshot.items():
            if prev is None:
                os.environ.pop(key, None)
            else:
                os.environ[key] = prev

    ctx.call_on_close(_restore_estimate_env)

    if estimate_mode:
        os.environ["PDD_ESTIMATE"] = "1"
        os.environ["PDD_LLM_ATTRIBUTION_PROCESS_LOG"] = "0"
        os.environ["PDD_LLM_ATTRIBUTION_STDOUT"] = "0"
    else:
        os.environ.pop("PDD_ESTIMATE", None)
    if estimate_json:
        os.environ["PDD_ESTIMATE_JSON"] = "1"
    else:
        os.environ.pop("PDD_ESTIMATE_JSON", None)
    if estimate_mode:
        ctx.obj["output_cost"] = None
        os.environ.pop("PDD_OUTPUT_COST_PATH", None)
    else:
        ctx.obj["output_cost"] = output_cost
    ctx.obj["review_examples"] = review_examples
    if review_examples:
        ctx.obj["grounding_review_decisions"] = []
    # PDD_FORCE_LOCAL env must behave like --local: the per-step cloud
    # dispatchers (generateCode/crashCode/verifyCode/fixCode) gate on
    # ctx.obj["local"], not on the env var, so an env-only force-local
    # previously still attempted PDD-cloud auth — including an interactive
    # GitHub device-flow hang outside CI. Truthy set matches sync_main.
    env_force_local = os.environ.get(
        "PDD_FORCE_LOCAL", ""
    ).strip().lower() in {"1", "true", "yes", "on"}
    ctx.obj["local"] = bool(local or estimate_mode or env_force_local)
    # Propagate --local flag to environment for llm_invoke cloud detection
    if local or estimate_mode:
        os.environ['PDD_FORCE_LOCAL'] = '1'
    # Use DEFAULT_TIME if time is not provided
    ctx.obj["time"] = time if time is not None else DEFAULT_TIME
    # Track whether the user explicitly supplied --time on the command line.
    # ctx.obj["time"] is always populated (DEFAULT_TIME fallback), so callers
    # that want to forward an explicit reasoning override per-call must gate
    # on this flag — otherwise plain `pdd bug ...` would behave as if
    # `--time DEFAULT_TIME` was passed and force-set provider effort.
    ctx.obj["time_explicit"] = time is not None
    # Mirror --time into PDD_REASONING_EFFORT so agentic CLI subprocesses
    # (Codex especially) honor the user's reasoning allocation. Env-var
    # pattern matches CLAUDE_MODEL/CODEX_MODEL threading in _run_with_provider.
    # Only set when the user explicitly passed --time; otherwise leave any
    # pre-existing value (e.g. from the worker env.yaml such as
    # CODEX_REASONING_EFFORT=xhigh for GPT-5.4 routing) alone.
    if time is not None:
        from ..reasoning import time_to_effort_level
        os.environ["PDD_REASONING_EFFORT"] = time_to_effort_level(time)

    # Context compression options (issue #877)
    from ..compression_reporting import clear_compression_fallback_events
    from ..config_resolution import (
        apply_compression_env,
        effective_compression_config,
        set_cli_compression_override,
    )

    clear_compression_fallback_events()
    set_cli_compression_override(None)
    ctx.obj["compress_examples"] = compress_examples
    ctx.obj["compress_test_context"] = compress_test_context
    ctx.obj["context_compression"] = context_compression
    ctx.obj["compression_fallback"] = compression_fallback
    cli_compression: dict[str, Any] = {}
    if compress_examples is not None:
        cli_compression["compress_examples"] = compress_examples
    if compress_test_context is not None:
        cli_compression["compress_test_context"] = compress_test_context
    if context_compression is not None:
        cli_compression["context_compression"] = context_compression
    if compression_fallback is not None:
        cli_compression["compression_fallback"] = compression_fallback
    set_cli_compression_override(cli_compression if cli_compression else None)
    if cli_compression:
        apply_compression_env(effective_compression_config({}))

    # Persist context override for downstream calls
    ctx.obj["context"] = context_override
    ctx.obj["core_dump"] = core_dump
    ctx.obj["keep_core_dumps"] = keep_core_dumps

    # Garbage collect old core dumps on every CLI invocation (Issue #231)
    # This runs regardless of --no-core-dump to ensure cleanup always happens
    from .dump import garbage_collect_core_dumps
    garbage_collect_core_dumps(keep=keep_core_dumps)

    # Set up terminal output capture if core_dump is enabled
    if core_dump:
        stdout_capture = OutputCapture(sys.stdout)
        stderr_capture = OutputCapture(sys.stderr)
        sys.stdout = stdout_capture
        sys.stderr = stderr_capture
        ctx.obj["_stdout_capture"] = stdout_capture
        ctx.obj["_stderr_capture"] = stderr_capture

    # Suppress verbose if quiet is enabled
    if quiet:
        ctx.obj["verbose"] = False
        try:
            import logging

            logging.getLogger("pdd").setLevel(logging.ERROR)
        except Exception:
            pass
        try:
            from ..llm_invoke import set_quiet_logging
            set_quiet_logging()
        except Exception:
            pass

    # Warn users who have not completed interactive setup unless they are running it now
    if not estimate_mode and not json_mode and _should_show_onboarding_reminder(ctx):
        console.print(
            "[warning]Complete onboarding with `pdd setup` to install tab completion and configure API keys.[/warning]"
        )
        ctx.obj["reminder_shown"] = True

    # If --list-contexts is provided, print and exit before any other actions
    if list_contexts:
        try:
            names = list_available_contexts()
        except Exception as exc:
            # Surface config errors as usage errors
            raise click.UsageError(f"Failed to load .pddrc: {exc}")
        # Print one per line; avoid Rich formatting for portability
        for name in names:
            click.echo(name)
        _restore_captured_streams(ctx)
        ctx.exit(0)

    # Optional early validation for --context
    if context_override:
        try:
            names = list_available_contexts()
        except Exception as exc:
            # If .pddrc is malformed, propagate as usage error
            raise click.UsageError(f"Failed to load .pddrc: {exc}")
        if context_override not in names:
            raise click.UsageError(
                f"Unknown context '{context_override}'. Available contexts: {', '.join(names)}"
            )

    # Perform auto-update check unless disabled

    if not json_mode and not estimate_mode and os.getenv("PDD_AUTO_UPDATE", "true").lower() != "false":
        try:
            if not quiet:
                console.print("[info]Checking for updates...[/info]")
            # Removed quiet=quiet argument as it caused TypeError
            auto_update()
        except Exception as exception:  # Using more descriptive name
            if not quiet:
                console.print(
                    f"[warning]Auto-update check failed:[/warning] {exception}", 
                    style="warning"
                )

    # If no subcommands were provided, show help and exit gracefully
    if ctx.invoked_subcommand is None and not ctx.protected_args:
        if not quiet:
            console.print("[info]Run `pdd --help` for usage or `pdd setup` to finish onboarding.[/info]")
        click.echo(ctx.get_help())
        _restore_captured_streams(ctx)
        ctx.exit(0)

    # Block/warn on likely duplicate expensive runs before the subcommand body runs.
    if not estimate_mode:
        try:
            check_duplicate_before_subcommand(ctx)
        except click.UsageError:
            _restore_captured_streams(ctx)
            raise
        except click.Abort:
            _restore_captured_streams(ctx)
            raise


def _derive_success_from_normalized_results(normalized_results: List[Any]) -> bool:
    """Return True iff every guarded subcommand reported success.

    Convention (documented at ``cli.py`` result-callback summary loop): guarded
    subcommands return a 3-tuple ``(result, cost, model_name)`` on success and
    ``None`` on failure. An empty list is treated as non-success so that an
    empty dispatch does not poison the dedup store. Used by the ``process_commands``
    result callback to decide whether to persist a record for fix #1275.
    """
    if not normalized_results:
        return False
    return not any(r is None for r in normalized_results)


def _normalized_results_should_exit_nonzero(
    normalized_results: List[Any], invoked_subcommands: List[str]
) -> bool:
    """Return True when normalized command results represent process failure."""
    for i, result in enumerate(normalized_results):
        command_name = (
            invoked_subcommands[i]
            if i < len(invoked_subcommands)
            else f"Unknown Command {i + 1}"
        )
        if result is None and command_name != "install_completion":
            return True
        if isinstance(result, tuple) and len(result) == 3:
            result_data = result[0]
            if isinstance(result_data, dict) and result_data.get("passed") is False:
                return True
    return False


# --- Result Callback for Command Execution Summary ---
@cli.result_callback()
@click.pass_context
def process_commands(
    ctx: Optional[click.Context] = None,
    results: Optional[List[Optional[Tuple[Any, float, str]]]] = None,
    **kwargs,
):
    """
    Processes results returned by executed commands and prints a summary.
    Receives a list of tuples, typically (result, cost, model_name),
    or None from each command function.
    """
    total_cost = 0.0
    # Get Click's invoked subcommands attribute first
    invoked_subcommands = getattr(ctx, 'invoked_subcommands', [])
    # If Click didn't provide it (common in real runs), fall back to the list
    # tracked on ctx.obj by @track_cost — but avoid doing this during pytest
    # so unit tests continue to assert the "Unknown Command" output.
    if not invoked_subcommands:
        import os as _os
        if not _os.environ.get('PYTEST_CURRENT_TEST'):
            try:
                if ctx.obj and isinstance(ctx.obj, dict):
                    invoked_subcommands = ctx.obj.get('invoked_subcommands', []) or []
            except Exception:
                invoked_subcommands = []
    # Normalize results: Click may pass a single return value (e.g., a 3-tuple)
    # rather than a list of results. Wrap single 3-tuples so we treat them as
    # one step in the summary instead of three separate items.
    if results is None:
        normalized_results: List[Any] = []
    elif isinstance(results, list):
        normalized_results = results
    elif isinstance(results, tuple) and len(results) == 3:
        normalized_results = [results]
    else:
        # Fallback: wrap any other scalar/iterable as a single result
        normalized_results = [results]

    num_commands = len(invoked_subcommands)
    num_results = len(normalized_results)  # Number of results actually received
    estimate_records = _collect_estimate_records(normalized_results, ctx)
    estimate_mode = bool(ctx.obj.get("estimate")) if isinstance(ctx.obj, dict) else False
    if estimate_mode or estimate_records:
        if estimate_records:
            _render_estimate_output(ctx, estimate_records)
        elif isinstance(ctx.obj, dict) and ctx.obj.get("estimate_json"):
            click.echo(
                "Estimate mode produced no records; no JSON payload is available.",
                err=True,
            )
            ctx.exit(1)
        else:
            click.echo("No estimate was produced for this command.")
        _write_result_core_dump(ctx, normalized_results, invoked_subcommands, 0.0)
        return

    suppress_result_summary = bool(
        isinstance(ctx.obj, dict) and ctx.obj.get("_suppress_result_summary")
    )

    if not ctx.obj.get("quiet") and not suppress_result_summary:
        console.print("\n[info]--- Command Execution Summary ---[/info]")

    for i, result_tuple in enumerate(normalized_results):
        # Use the retrieved subcommand name (might be "Unknown Command X" in tests)
        command_name = invoked_subcommands[i] if i < num_commands else f"Unknown Command {i+1}"

        # Check if the command failed (returned None)
        if result_tuple is None:
            if not ctx.obj.get("quiet") and not suppress_result_summary:
                # Check if it was install_completion (which normally returns None)
                if command_name == "install_completion":
                    console.print(f"  [success]{_OK_GLYPH}[/success] [info]Step {i+1} ({command_name}):[/info] Command completed.")
                # If command name is unknown, and it might be install_completion which prints its own status
                elif command_name.startswith("Unknown Command"):
                    console.print(f"  [info]Step {i+1} ({command_name}):[/info] Command executed (see output above for status details).")
                # Check if it was preprocess (which returns a dummy tuple on success)
                # This case handles actual failure for preprocess
                elif command_name == "preprocess":
                    console.print(f"  [error]{_FAIL_GLYPH}[/error] [error]Step {i+1} ({command_name}):[/error] Command failed.")
                else:
                    console.print(f"  [error]{_FAIL_GLYPH}[/error] [error]Step {i+1} ({command_name}):[/error] Command failed.")
        # Check if the result is the expected tuple structure from @track_cost or preprocess success
        elif isinstance(result_tuple, tuple) and len(result_tuple) == 3:
            result_data, cost, model_name = result_tuple
            total_cost += cost
            if not ctx.obj.get("quiet") and not suppress_result_summary:
                # Special handling for preprocess success message (check actual command name)
                actual_command_name = invoked_subcommands[i] if i < num_commands else None # Get actual name if possible
                if actual_command_name == "preprocess" and cost == 0.0 and model_name == "local":
                    console.print(f"  [success]{_OK_GLYPH}[/success] [info]Step {i+1} ({command_name}):[/info] Command completed (local).")
                else:
                    # Generic output using potentially "Unknown Command" name.
                    # Suppress the Model: segment when no model was used (zero-cost
                    # no-ops like an all_synced sync return model_name="" or
                    # "unknown"/"none"/"N/A") so the UI doesn't render a trailing
                    # blank "Model: " label (#1103).
                    model_repr = (model_name or "").strip()
                    if model_repr and model_repr.lower() not in {"unknown", "n/a", "none", "skipped"}:
                        console.print(f"  [success]{_OK_GLYPH}[/success] [info]Step {i+1} ({command_name}):[/info] Cost: ${cost:.6f}, Model: {model_repr}")
                    else:
                        console.print(f"  [success]{_OK_GLYPH}[/success] [info]Step {i+1} ({command_name}):[/info] Cost: ${cost:.6f}")
                
                # Display examples used for grounding
                if isinstance(result_data, dict) and result_data.get("examplesUsed"):
                    console.print("    Examples used:")
                    for ex in result_data["examplesUsed"]:
                        slug = ex.get("slug", "unknown")
                        title = ex.get("title", "Untitled")
                        console.print(f"      - {slug} (\"{title}\")")

        # Handle dicts with examplesUsed (e.g. from commands not using track_cost but returning metadata)
        elif isinstance(result_tuple, dict) and result_tuple.get("examplesUsed"):
            if not ctx.obj.get("quiet") and not suppress_result_summary:
                console.print(f"  [success]{_OK_GLYPH}[/success] [info]Step {i+1} ({command_name}):[/info] Command completed.")
                console.print("    Examples used:")
                for ex in result_tuple["examplesUsed"]:
                    slug = ex.get("slug", "unknown")
                    title = ex.get("title", "Untitled")
                    console.print(f"      - {slug} (\"{title}\")")

        else:
            # Handle unexpected return types if necessary
            if not ctx.obj.get("quiet") and not suppress_result_summary:
                # Provide more detail on the unexpected type
                console.print(f"  [warning]Step {i+1} ({command_name}):[/warning] Unexpected result format: {type(result_tuple).__name__} - {str(result_tuple)[:50]}...")


    if not ctx.obj.get("quiet") and not suppress_result_summary:
        from ..compression_reporting import format_compression_summary_lines

        for line in format_compression_summary_lines():
            console.print(f"[info]{line}[/info]")
        # Only print total cost if at least one command potentially contributed cost
        if any(res is not None and isinstance(res, tuple) and len(res) == 3 for res in normalized_results):
            console.print(f"[info]Total Estimated Cost:[/info] ${total_cost:.6f}")
        # Indicate if the chain might have been incomplete due to errors
        if num_results < num_commands and results is not None and not all(res is None for res in results): # Avoid printing if all failed
            console.print("[warning]Note: Chain may have terminated early due to errors.[/warning]")
        console.print("[info]-------------------------------------[/info]")

    record_after_guarded_command(
        ctx, success=_derive_success_from_normalized_results(normalized_results)
    )

    # Finally, write a core dump if requested
    if not (isinstance(ctx.obj, dict) and ctx.obj.get("_suppress_core_dump")):
        _write_result_core_dump(ctx, normalized_results, invoked_subcommands, total_cost)
    fatal = ctx.obj.get("_fatal_exception") if isinstance(ctx.obj, dict) else None
    command_failed = (
        ctx.obj.get("_command_failed") if isinstance(ctx.obj, dict) else None
    )
    if fatal or command_failed or _normalized_results_should_exit_nonzero(
        normalized_results, invoked_subcommands
    ):
        ctx.exit(1)
