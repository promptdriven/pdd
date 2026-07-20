"""
One-session sync: run example, crash-fix, verify, test, and fix steps
in a single agentic session instead of separate sessions per step.
"""

import ast
import logging
import os
import re
import sys
import threading
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

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
from .content_selector import _warn_on_shadow_test
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

# Marker emitted to stdout when the churn gate accepts a large but
# coverage-preserving rewrite on exhaustion (see
# ``_accept_churn_rewrite_on_exhaustion``). Parseable by the cloud runner the
# same way ``PDD_PHASE:`` markers are.
_TEST_CHURN_ACCEPTED_MARKER = "PDD_TEST_CHURN_ACCEPTED"

# --- Coverage measurement for the accept-on-exhaustion churn gate (#2208) ---
# Textual churn (difflib line ratio) over-fires on a legitimate large test
# rewrite: when a prompt/code change is substantial the regenerated test is
# ~100% different yet correct. The repair-directive retry cannot reduce genuine
# churn, so the gate hard-fails an already-successful agentic result. To
# auto-recover we accept the rewrite on exhaustion ONLY when it preserves
# coverage — measured by counting test cases and assertions per language.
_JS_TEST_EXTS = {".ts", ".tsx", ".js", ".jsx", ".mjs", ".cjs"}
# Test-case keywords must start at a statement boundary so a method call like
# ``client.test(`` is NOT counted, but modifier chains (``it.skip``,
# ``test.concurrent.each``) are. Assertions may be globals (``expect(``) or
# method forms (``chai.expect(``, ``assert.equal(``)).
_JS_TEST_CASE_RE = re.compile(r"(?<![.\w])(?:it|test)(?:\.\w+)*\s*\(")
_JS_ASSERTION_RE = re.compile(r"\b(?:expect|assert)(?:\.\w+)*\s*\(")


def _count_test_units(text: str, output_path: str) -> Optional[Tuple[int, int]]:
    """Return ``(test_case_count, assertion_count)`` for a measurable language.

    Returns ``None`` when the file is one we cannot reliably measure — anything
    other than Python or TS/JS, or Python source that does not parse — so the
    caller stays on the strict churn gate rather than guessing at coverage.
    Comments and string/docstring literals are excluded so a rewrite cannot pad
    its count with commented-out or quoted ``assert``/``expect`` text.
    """
    suffix = Path(output_path).suffix.lower()
    if suffix == ".py":
        return _count_python_test_units(text or "")
    if suffix in _JS_TEST_EXTS:
        return _count_js_test_units(text or "")
    return None


def _count_python_test_units(text: str) -> Optional[Tuple[int, int]]:
    """Count Python ``test*`` functions + assertions via the AST.

    The AST ignores comments and string/docstring literals natively. Returns
    ``None`` for source that does not parse, so a syntactically broken rewrite
    is never auto-accepted.
    """
    try:
        tree = ast.parse(text)
    except (SyntaxError, ValueError):
        # SyntaxError = not valid Python; ValueError = e.g. embedded null bytes.
        # Either way the source is unmeasurable -> stay on the strict gate.
        return None
    cases = 0
    assertions = 0
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if node.name.startswith("test"):
                cases += 1
        elif isinstance(node, ast.Assert):
            assertions += 1
        elif isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
            attr = node.func.attr
            if attr.startswith("assert") or attr == "raises":
                assertions += 1
    return (cases, assertions)


# Characters after which a ``/`` begins a regex literal (expression position)
# rather than division. When ambiguous we err toward division (keep as code) —
# a wrong guess only mis-counts symmetrically and can never cause a false
# accept on its own. ``<`` and ``>`` are deliberately EXCLUDED: in TSX a ``/``
# that follows ``<`` is a JSX closing tag (``</Provider>``), not a regex, and a
# real regex literal essentially never follows a ``<``/``>`` comparison in test
# code — including them made ``_strip_js_noncode`` treat the slash in
# ``</tag>`` as a regex opener and strip the rest of the line, silently
# dropping any assertions written after the closing tag on the same line
# (a common compact-React-test shape, e.g.
# ``render(<Provider><Widget /></Provider>); expect(a); expect(b);``).
_REGEX_PREV_CHARS = frozenset("(,=:[!&|?{;}+-*%^~")


def _strip_js_noncode(text: str) -> str:
    """Replace JS/TS comments, string/regex literals, and template *text* with
    spaces in a single pass, while KEEPING executable code.

    A hand scanner (not chained regexes) is required so that: a ``//`` inside a
    string (e.g. a ``http://`` URL) is not mistaken for a comment; a quote inside
    a comment is not mistaken for a string; a regex literal like ``/expect(/``
    cannot pad the assertion count; JSX tag slashes — both the closing-tag
    ``</Provider>`` and the self-closing ``<Widget />`` / ``<Widget count={n} />``
    forms — are treated as code rather than regex openers, so assertions written
    after a tag on the SAME line (a common compact-React-test shape) are NOT
    swallowed; and an executable ``${ expect(x) }`` interpolation inside a
    template literal is still counted (its interior is stripped recursively as
    code). Residual: a brace inside a string inside a template interpolation can
    mis-delimit the interpolation — a third-order case tolerated because
    measurement is symmetric and downstream verification is the backstop.
    """
    out: List[str] = []
    i, n = 0, len(text)
    prev_sig = ""  # last significant (non-space) code char, for regex detection
    while i < n:
        c = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if c == "/" and nxt == "/":  # line comment
            i += 2
            while i < n and text[i] != "\n":
                i += 1
            out.append(" ")
        elif c == "/" and nxt == "*":  # block comment
            i += 2
            while i < n and not (text[i] == "*" and text[i + 1 : i + 2] == "/"):
                i += 1
            i += 2
            out.append(" ")
        elif c == "/" and nxt == ">":  # JSX self-closing tag '/>': keep as code
            # ``<Widget />`` / ``<Widget count={n} />`` — the char before the
            # ``/`` (e.g. ``}`` from a ``{expr}`` attribute) can be in
            # ``_REGEX_PREV_CHARS``, so guard on the following ``>`` to stop the
            # self-closing slash from being misread as a regex opener and
            # swallowing any same-line assertions after the tag.
            out.append(c)
            prev_sig = c
            i += 1
        elif c == "/" and prev_sig in _REGEX_PREV_CHARS:  # regex literal
            i += 1
            while i < n and text[i] not in ("/", "\n"):
                i += 2 if text[i] == "\\" else 1
            if i < n and text[i] == "/":
                i += 1
            out.append(" ")
        elif c in "'\"":  # string literal (single line)
            quote = c
            i += 1
            while i < n and text[i] != quote and text[i] != "\n":
                i += 2 if text[i] == "\\" else 1
            if i < n and text[i] == quote:
                i += 1
            out.append(" ")
        elif c == "`":  # template literal: strip text, keep ${...} as code
            i += 1
            while i < n and text[i] != "`":
                if text[i] == "\\":
                    i += 2
                    continue
                if text[i] == "$" and text[i + 1 : i + 2] == "{":
                    i += 2
                    start = i
                    depth = 1
                    while i < n and depth > 0:
                        if text[i] == "{":
                            depth += 1
                        elif text[i] == "}":
                            depth -= 1
                            if depth == 0:
                                break
                        i += 1
                    out.append(" ")
                    out.append(_strip_js_noncode(text[start:i]))
                    out.append(" ")
                    if i < n and text[i] == "}":
                        i += 1
                else:
                    i += 1
            if i < n and text[i] == "`":
                i += 1
            out.append(" ")
        else:
            out.append(c)
            if not c.isspace():
                prev_sig = c
            i += 1
    return "".join(out)


def _count_js_test_units(text: str) -> Tuple[int, int]:
    """Count TS/JS test cases (``it``/``test``) + assertions (``expect``/
    ``assert``) after removing comments and string/template literals."""
    stripped = _strip_js_noncode(text)
    return (
        len(_JS_TEST_CASE_RE.findall(stripped)),
        len(_JS_ASSERTION_RE.findall(stripped)),
    )


def _candidate_preserves_coverage(
    pre_text: str, candidate_text: Optional[str], output_path: str
) -> bool:
    """True when ``candidate_text`` is a safe, coverage-preserving rewrite.

    Accept only when, for a measurable language, the candidate keeps at least as
    many test cases AND assertions as the pre-session file and carries at least
    one real assertion. A deleted candidate (``None``), an unmeasurable language,
    or an assertion-free rewrite is never accepted, so deletions, unknown
    formats, and vacuous rewrites keep the strict churn gate.
    """
    if candidate_text is None:
        return False
    pre_counts = _count_test_units(pre_text, output_path)
    post_counts = _count_test_units(candidate_text, output_path)
    if pre_counts is None or post_counts is None:
        return False
    pre_cases, pre_asserts = pre_counts
    post_cases, post_asserts = post_counts
    return (
        post_cases >= pre_cases
        and post_asserts >= pre_asserts
        and post_asserts >= 1
    )


def _same_path(a: Path, b: Path) -> bool:
    """Best-effort same-file check tolerant of missing files (mirrors the sweep)."""
    try:
        return a.samefile(b)
    except OSError:
        try:
            return a.resolve() == b.resolve()
        except OSError:
            return False


def _safe_read_text(path: Path) -> Optional[str]:
    """Read ``path`` as UTF-8, returning ``None`` if it is missing/unreadable."""
    try:
        return path.read_text(encoding="utf-8")
    except OSError:
        return None


def _safe_write_text(path: Path, content: str) -> bool:
    """UTF-8 write, creating parents. Returns True on success, False on
    ``OSError`` so callers can detect (and refuse to claim) a failed reapply."""
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
        return True
    except OSError:
        return False


def _accept_churn_rewrite_on_exhaustion(
    *,
    code_path: Path,
    test_path: Optional[Path],
    canonical_existed: bool,
    existing_code_content: Optional[str],
    existing_test_content: Optional[str],
    pre_test_contents: Dict[Path, str],
    candidate_code: Optional[str],
    candidate_tests: Dict[Path, Optional[str]],
    quiet: bool,
) -> bool:
    """Decide + apply accept-on-exhaustion for one-session test churn (#2208).

    When constrained recovery cannot drop textual churn below threshold, accept
    the agent's rewrite instead of hard-failing IFF every guarded pre-existing
    test file (canonical + alt-path) is a coverage-preserving rewrite
    (``_candidate_preserves_coverage``). On accept, the agent's candidate bytes
    — reverted by the caller's restore — are reapplied to disk and the
    ``PDD_TEST_CHURN_ACCEPTED`` marker is emitted. Returns False otherwise,
    leaving the restored pre-session files in place so the caller hard-fails as
    before. Operators can force the strict gate with
    ``PDD_DISABLE_TEST_CHURN_AUTOACCEPT``.
    """
    if _env_flag_enabled("PDD_DISABLE_TEST_CHURN_AUTOACCEPT"):
        return False

    # Accepting reapplies the agent's CODE alongside the accepted tests. If the
    # code file is unreadable/deleted (candidate_code is None) we cannot
    # faithfully restore the agent's state, so refuse rather than report success
    # with stale code bytes — important for non-Python outputs where the
    # public-surface gate is skipped.
    if candidate_code is None:
        return False

    # Build (output_path, pre_text, candidate_text) for every guarded file.
    protected: List[Tuple[str, str, Optional[str]]] = []
    if canonical_existed and test_path is not None and existing_test_content:
        protected.append(
            (str(test_path), existing_test_content, candidate_tests.get(test_path))
        )
    for snap_path, prior in pre_test_contents.items():
        if test_path is not None and _same_path(snap_path, test_path):
            continue  # canonical handled above
        protected.append((str(snap_path), prior, candidate_tests.get(snap_path)))

    # Require at least one file with real pre-session coverage, and that EVERY
    # such file is coverage-preserving. Empty/whitespace baselines carry no
    # coverage and are skipped.
    evaluated = False
    for output_path, pre_text, candidate_text in protected:
        if not pre_text or not pre_text.strip():
            continue
        evaluated = True
        if not _candidate_preserves_coverage(pre_text, candidate_text, output_path):
            return False
    if not evaluated:
        return False

    # Reapply the agent's candidate bytes the caller's restore reverted. If ANY
    # write fails, refuse the acceptance (return False) so the caller hard-fails
    # honestly rather than reporting success with stale pre-session bytes on
    # disk — and do not emit the accepted marker.
    write_ok = _safe_write_text(code_path, candidate_code)
    reapplied: List[Path] = []
    for path_obj, content in candidate_tests.items():
        if content is not None:
            write_ok = _safe_write_text(path_obj, content) and write_ok
            reapplied.append(path_obj)
    if not write_ok:
        # Roll back any partial reapply so the hard-fail path keeps its contract
        # — pre-session bytes on disk — rather than leaving a half-applied mix of
        # candidate and restored files. Best-effort, mirrors the caller's restore.
        if existing_code_content is not None:
            _safe_write_text(code_path, existing_code_content)
        if (
            canonical_existed
            and test_path is not None
            and existing_test_content is not None
        ):
            _safe_write_text(test_path, existing_test_content)
        for snap_path, prior in pre_test_contents.items():
            _safe_write_text(snap_path, prior)
        logger.warning(
            "Test-churn auto-accept aborted: could not reapply candidate bytes; "
            "rolled back to pre-session state and fell back to the strict gate."
        )
        return False

    accepted_label = (
        str(test_path)
        if test_path is not None
        else (", ".join(str(p) for p in reapplied) or "<alt-path>")
    )
    print(f"{_TEST_CHURN_ACCEPTED_MARKER}: {accepted_label}", flush=True)
    if not quiet:
        rprint(
            "[yellow]⚠ Test churn: accepted a large but coverage-preserving "
            "test rewrite after constrained recovery could not reduce churn; "
            "downstream verification is the pass/fail backstop.[/yellow]"
        )
    return True


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

    # Warn when a real test already exists at a path the runner collects but
    # the canonical pdd_files['test'] differs. One-session sync is the default
    # issue-sync path and writes code/test directly (never through
    # cmd_test_main), so without this it would be the one path where the
    # shadow/false-green fork (issue #1903) goes unwarned. Advisory only —
    # nothing is overwritten here.
    _warn_on_shadow_test(
        str(code_path),
        str(test_path) if test_path else None,
        quiet=quiet,
    )

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
                # Capture the agent's candidate bytes BEFORE the restore below
                # reverts them, so accept-on-exhaustion (#2208) can reapply a
                # coverage-preserving rewrite instead of hard-failing on textual
                # churn alone. A deleted file reads back as None and is never
                # accepted. Keyed by Path; canonical first, then every alt-path
                # snapshot the gate guards.
                churn_candidate_code = _safe_read_text(code_path)
                churn_candidate_tests: Dict[Path, Optional[str]] = {}
                if canonical_existed and test_path is not None:
                    churn_candidate_tests[test_path] = _safe_read_text(test_path)
                for snap_path in pre_test_contents:
                    if snap_path not in churn_candidate_tests:
                        churn_candidate_tests[snap_path] = _safe_read_text(snap_path)
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
                # Exhaustion is reached either when the retry produced the
                # identical churn signature (no progress — mirrors the
                # orchestration helper's short-circuit) or when the tighter
                # ``_MAX_TEST_CHURN_ATTEMPTS`` cap is hit (#1015 iter-1,
                # Important 2; surface repair uses a separate counter so the
                # two gates cannot eat each other's budget).
                identical_signature = (
                    last_churn_signature is not None
                    and signature == last_churn_signature
                )
                last_churn_signature = signature
                if (
                    identical_signature
                    or churn_attempts_used >= max_churn_attempts_for_churn
                ):
                    # Constrained recovery cannot reduce genuine churn. Before
                    # hard-failing, accept the rewrite IFF it preserves coverage
                    # (#2208): a legitimate large rewrite driven by a real
                    # prompt/code change should not be vetoed by textual churn.
                    # Otherwise fall through to the structured hard-failure block
                    # after the loop. (One-session only — `sync_orchestration`'s
                    # parallel churn loop intentionally keeps the strict gate.)
                    if _accept_churn_rewrite_on_exhaustion(
                        code_path=code_path,
                        test_path=test_path,
                        canonical_existed=canonical_existed,
                        existing_code_content=existing_code_content,
                        existing_test_content=existing_test_content,
                        pre_test_contents=pre_test_contents,
                        candidate_code=churn_candidate_code,
                        candidate_tests=churn_candidate_tests,
                        quiet=quiet,
                    ):
                        churn_gate_passed = True
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

    # sync_main's summary table reads result.get("summary") first and falls
    # through to result.get("error"); without summary on success, the success
    # row collapses to the "No details." fallback (#1103).
    if success:
        summary = f"One-session sync complete (operations: {', '.join(operations)})"
    else:
        summary = "; ".join(errors) if errors else "One-session sync failed"

    return {
        "success": success,
        # Use accumulated cost so failed-then-retried attempts charge the
        # operator for every agentic session run (mirrors the generate-op
        # cost accumulation in `sync_orchestration.py`).
        "total_cost": float(accumulated_cost or cost or 0.0),
        "model_name": accumulated_provider or provider,
        "operations_completed": operations,
        "errors": errors,
        "summary": summary,
        "error": "; ".join(errors) if errors else "",
    }
