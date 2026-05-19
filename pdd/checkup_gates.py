"""Deterministic gates for ``pdd checkup --pr --review-loop``.

The review loop's LLM reviewer (codex/claude/gemini) can declare a PR
"clean" while a fast, deterministic local check still fails on the
worktree (e.g. ``prettier --check`` finds unformatted files). This
module discovers a conservative, allowlisted set of repo-local gates,
runs each as a bounded list-form subprocess, and converts failures into
synthetic blocker ``ReviewFinding`` entries that the review loop must
treat exactly like reviewer findings: refuse the clean verdict, feed
them to the fixer, and re-run gates on the next round.

Trust-boundary invariants:
* All commands are list-form. ``shell=True`` is never used.
* Discovery is allowlist-only. Anything not explicitly recognized is
  skipped, not best-effort guessed.
* The runner never raises. ``subprocess.run`` errors are captured as
  ``GateResult`` rows with ``exit_code=None`` and a non-empty ``error``.
* All stdout/stderr is truncated to roughly 10KB each side and scrubbed
  via ``pdd.checkup_review_loop._scrub_secrets`` before persistence or
  rendering.
* Environment is scrubbed: ``CI=1``, ``NO_COLOR=1``, ``FORCE_COLOR=0`` are
  injected; ``PDD_*`` mutating envs are stripped so a gate cannot inherit
  reviewer/fixer state.
* The runner's ``cwd`` is always the loop-owned PR worktree.
"""

from __future__ import annotations

import datetime as _dt
import json
import logging
import os
import re
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

logger = logging.getLogger(__name__)


# Approximate per-stream excerpt cap. Bounded to keep prompt injection
# tractable and to keep persisted artifacts small. We leave a generous
# margin over the literal byte count so a small "[truncated]" marker
# fits without violating the integration-side budget contract.
_EXCERPT_LIMIT = 10_000

# Per-gate default timeout in seconds. The runner enforces this even
# when ``Gate.timeout`` is left at the dataclass default so a discovery
# bug cannot wedge the review loop.
DEFAULT_GATE_TIMEOUT_SECONDS: float = 60.0


# ---------------------------------------------------------------------------
# Dataclasses
# ---------------------------------------------------------------------------


@dataclass
class Gate:
    """A single discovered deterministic gate.

    The ``cmd`` field is the literal list-form argv. The runner
    ``run_gates`` is responsible for spawning the subprocess; this
    dataclass is data only.
    """

    name: str
    cmd: List[str]
    source: str
    severity: str = "blocker"
    timeout: float = DEFAULT_GATE_TIMEOUT_SECONDS
    area: str = "deterministic-gate"
    required_fix_hint: str = ""

    def to_dict(self) -> Dict[str, object]:
        return {
            "name": self.name,
            "cmd": list(self.cmd),
            "source": self.source,
            "severity": self.severity,
            "timeout": self.timeout,
            "area": self.area,
            "required_fix_hint": self.required_fix_hint,
        }


@dataclass
class GateResult:
    """Result of executing a single gate.

    ``exit_code is None`` indicates a runner-side failure (timeout,
    missing binary, OSError). In that case ``error`` carries a short
    human-readable description and the gate is treated as a failure by
    ``gate_results_to_findings``.
    """

    gate: Gate
    exit_code: Optional[int]
    stdout_excerpt: str
    stderr_excerpt: str
    duration_seconds: float
    started_at_iso: str
    error: str = ""

    @property
    def passed(self) -> bool:
        return self.exit_code == 0

    def to_dict(self) -> Dict[str, object]:
        return {
            "gate": self.gate.to_dict(),
            "exit_code": self.exit_code,
            "stdout_excerpt": self.stdout_excerpt,
            "stderr_excerpt": self.stderr_excerpt,
            "duration_seconds": self.duration_seconds,
            "started_at_iso": self.started_at_iso,
            "error": self.error,
            "passed": self.passed,
        }


# ---------------------------------------------------------------------------
# Discovery
# ---------------------------------------------------------------------------


# npm script names this module recognizes as deterministic gates. Anything
# else is skipped: discovery is allowlist-only on purpose.
_RECOGNIZED_NPM_SCRIPTS: Tuple[str, ...] = (
    "format:check",
    "prettier:check",
    "lint:check",
    "typecheck",
    "tsc",
    "tsc:noemit",
)

# Substrings whose presence in an npm script command disqualifies the
# script entirely. Mutation, install, or deployment scripts must never
# run from a checkup gate.
_FORBIDDEN_SCRIPT_FRAGMENTS: Tuple[str, ...] = (
    "--write",
    "--fix",
    "install",
    "publish",
    "deploy",
    "start",
    " build",
    "build:",
    "git push",
    "rm -",
    "rimraf",
)


# Heads (after stripping the package manager prefix like ``npm run``) that
# we accept as gate-style commands.
_ACCEPTABLE_SCRIPT_HEADS: Tuple[str, ...] = (
    "prettier --check",
    "tsc --noemit",
    "tsc -p",
    "eslint",  # ``eslint`` alone is only accepted when no fix flag appears.
)


def _detect_node_runner(worktree: Path) -> str:
    """Return the package manager binary to invoke for npm scripts.

    Prefers ``pnpm``/``yarn``/``bun`` lockfiles over plain ``npm``. The
    return value is the literal argv[0]; the caller appends ``run`` +
    script name.
    """
    if (worktree / "pnpm-lock.yaml").exists():
        return "pnpm"
    if (worktree / "yarn.lock").exists():
        return "yarn"
    if (worktree / "bun.lockb").exists():
        return "bun"
    return "npm"


def _script_is_acceptable(command: str) -> bool:
    """Return True when an npm-script command-string is allowlisted."""
    if not command:
        return False
    lowered = command.lower()
    for forbidden in _FORBIDDEN_SCRIPT_FRAGMENTS:
        if forbidden in lowered:
            return False
    # Strip leading package-manager prefix so that
    # ``npm run format:check`` and ``yarn format:check`` both reduce to
    # the recognised tool head.
    stripped = lowered
    for prefix in (
        "npm run ",
        "yarn run ",
        "pnpm run ",
        "bun run ",
        "npx ",
        "yarn ",
        "pnpm ",
        "bun ",
    ):
        if stripped.startswith(prefix):
            stripped = stripped[len(prefix) :].lstrip()
            break
    for head in _ACCEPTABLE_SCRIPT_HEADS:
        if stripped.startswith(head):
            # eslint without an explicit ``--fix``/no-fix marker — the
            # script could mutate the worktree on certain configs, so
            # we require an explicit ``--no-fix`` to opt in.
            if head == "eslint" and "--fix" in stripped:
                return False
            return True
    return False


def _discover_npm_gates(worktree: Path) -> List[Gate]:
    package_json = worktree / "package.json"
    if not package_json.is_file():
        return []
    try:
        data = json.loads(package_json.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        logger.debug("checkup-gates: package.json unreadable: %s", exc)
        return []
    scripts = data.get("scripts") or {}
    if not isinstance(scripts, dict):
        return []
    runner = _detect_node_runner(worktree)
    gates: List[Gate] = []
    for script_name, script_command in scripts.items():
        if script_name not in _RECOGNIZED_NPM_SCRIPTS:
            continue
        if not isinstance(script_command, str):
            continue
        if not _script_is_acceptable(script_command):
            continue
        gates.append(
            Gate(
                name=f"npm:{script_name}",
                cmd=[runner, "run", script_name],
                source=f"package.json:scripts.{script_name}",
                required_fix_hint=(
                    f"Run `{runner} run {script_name}` locally and address the "
                    "reported issues."
                ),
            )
        )
    # If a typescript config exists and we did not emit a typecheck
    # script, try ``npx tsc --noEmit`` directly. Discovery rule: only when
    # ``typescript`` appears in the dependency map AND ``tsconfig.json``
    # exists.
    if (
        (worktree / "tsconfig.json").exists()
        and "npm:typecheck" not in {g.name for g in gates}
        and "npm:tsc" not in {g.name for g in gates}
        and "npm:tsc:noemit" not in {g.name for g in gates}
    ):
        deps: Dict[str, object] = {}
        for key in ("dependencies", "devDependencies", "peerDependencies"):
            value = data.get(key) or {}
            if isinstance(value, dict):
                deps.update(value)
        if "typescript" in deps and shutil.which("npx"):
            gates.append(
                Gate(
                    name="tsc-noemit",
                    cmd=["npx", "tsc", "--noEmit"],
                    source="tsconfig.json",
                    required_fix_hint=(
                        "Run `npx tsc --noEmit` locally and fix the reported "
                        "TypeScript errors."
                    ),
                )
            )
    return gates


def _discover_python_gates(
    worktree: Path, changed_files: Sequence[str]
) -> List[Gate]:
    gates: List[Gate] = []
    changed_py = [
        rel for rel in changed_files if rel.endswith(".py") and (worktree / rel).is_file()
    ]
    for rel in changed_py:
        gates.append(
            Gate(
                name=f"py-compile:{rel}",
                cmd=[sys.executable, "-m", "py_compile", str(worktree / rel)],
                source=rel,
                required_fix_hint=(
                    f"Fix the syntax error in {rel} so `python -m py_compile` "
                    "succeeds."
                ),
            )
        )
    pyproject = worktree / "pyproject.toml"
    pyproject_text = ""
    if pyproject.is_file():
        try:
            pyproject_text = pyproject.read_text(encoding="utf-8")
        except OSError as exc:
            logger.debug("checkup-gates: pyproject.toml unreadable: %s", exc)
            pyproject_text = ""

    def _tool_section_present(section: str) -> bool:
        if not pyproject_text:
            return False
        return bool(
            re.search(
                rf"^\s*\[\s*tool\.{re.escape(section)}\s*\](?:\s|$)",
                pyproject_text,
                re.MULTILINE,
            )
        )

    if changed_py and _tool_section_present("ruff") and shutil.which("ruff"):
        gates.append(
            Gate(
                name="ruff",
                cmd=["ruff", "check", *changed_py],
                source="pyproject.toml:[tool.ruff]",
                required_fix_hint=(
                    "Run `ruff check --fix` locally and address the remaining "
                    "issues."
                ),
            )
        )
    if changed_py and _tool_section_present("black") and shutil.which("black"):
        gates.append(
            Gate(
                name="black",
                cmd=["black", "--check", *changed_py],
                source="pyproject.toml:[tool.black]",
                required_fix_hint=(
                    "Run `black .` locally and commit the formatting changes."
                ),
            )
        )
    if changed_py and _tool_section_present("mypy") and shutil.which("mypy"):
        gates.append(
            Gate(
                name="mypy",
                cmd=["mypy", *changed_py],
                source="pyproject.toml:[tool.mypy]",
                required_fix_hint=(
                    "Run `mypy` locally and fix the reported type errors."
                ),
            )
        )
    return gates


def _git_diff_check_gate() -> Gate:
    return Gate(
        name="git-diff-check",
        cmd=["git", "diff", "--check"],
        source="git",
        required_fix_hint=(
            "Run `git diff --check` locally and fix the whitespace/conflict "
            "marker issues it reports."
        ),
    )


def _is_git_worktree(worktree: Path) -> bool:
    """Return True when ``worktree`` is inside a git checkout.

    A non-git directory (typical in unit tests that mock
    ``_setup_pr_worktree``) cannot run ``git diff --check``, so the
    gate is omitted to keep the loop's existing fail-open contract for
    those callers. Production review loops always run inside a real
    ``git fetch pull/N/head`` worktree so this guard is invisible there.
    """
    if (worktree / ".git").exists():
        return True
    try:
        result = subprocess.run(
            ["git", "-C", str(worktree), "rev-parse", "--is-inside-work-tree"],
            capture_output=True,
            text=True,
            check=False,
            timeout=5,
        )
    except (OSError, subprocess.SubprocessError):
        return False
    return result.returncode == 0 and result.stdout.strip() == "true"


def discover_gates(
    worktree: Path,
    changed_files: Sequence[str],
    *,
    extra_allow: Sequence[str] = (),
) -> List[Gate]:
    """Return the conservative deterministic gate set for ``worktree``.

    ``changed_files`` is the PR's changed-file inventory (POSIX relative
    paths). It scopes per-file gates such as ``py_compile``, ``ruff``,
    ``black`` and ``mypy``.

    ``extra_allow`` is a tuple of additional gate-name allowlist entries
    supplied by the operator. Currently this is a forward-compatibility
    hook: every discovered gate is allowlist-only and ``extra_allow`` is
    threaded through but not yet used to widen discovery. The argument is
    accepted so the CLI surface and the discovery surface can co-evolve
    without breaking signature stability.
    """
    _ = extra_allow  # reserved for v2; CLI plumbing already passes it through.
    gates: List[Gate] = []
    if _is_git_worktree(worktree):
        gates.append(_git_diff_check_gate())
    gates.extend(_discover_npm_gates(worktree))
    gates.extend(_discover_python_gates(worktree, changed_files))
    # Stable order: git-diff-check first, then language-specific gates
    # in discovery order. The runner walks the list left-to-right so
    # operators see consistent artifact filenames across rounds.
    return gates


# ---------------------------------------------------------------------------
# Execution
# ---------------------------------------------------------------------------


def _truncate(text: str) -> str:
    """Truncate ``text`` to roughly ``_EXCERPT_LIMIT`` characters.

    When truncation actually fires, append a short marker so an operator
    can tell that the artifact is incomplete.
    """
    if text is None:
        return ""
    if len(text) <= _EXCERPT_LIMIT:
        return text
    marker = "\n[...truncated]\n"
    keep = _EXCERPT_LIMIT - len(marker)
    return text[:keep] + marker


def _safe_slug(name: str) -> str:
    """Filesystem-safe slug for ``name``."""
    return re.sub(r"[^A-Za-z0-9._-]+", "_", name)[:120] or "gate"


def _build_subprocess_env() -> Dict[str, str]:
    """Build the environment dict the runner injects for each gate.

    Inherits the caller's PATH/HOME (so tools resolve), strips ``PDD_*``
    envs (so the gate cannot inherit reviewer/fixer state or token
    files), and forces ``CI=1``, ``NO_COLOR=1``, ``FORCE_COLOR=0`` for
    deterministic non-interactive output.
    """
    env = {
        key: value
        for key, value in os.environ.items()
        if not key.startswith("PDD_")
    }
    env["CI"] = "1"
    env["NO_COLOR"] = "1"
    env["FORCE_COLOR"] = "0"
    return env


def _scrub(text: str) -> str:
    """Run the loop's secret-scrubber over ``text``.

    Imported lazily to avoid an import cycle at module load: the review
    loop module imports ``checkup_gates``, not the other way around.
    """
    try:
        from .checkup_review_loop import _scrub_secrets

        return _scrub_secrets(text)
    except Exception as exc:  # pragma: no cover - defensive
        logger.debug("checkup-gates: secret scrub fell back: %s", exc)
        return text


def _now_iso() -> str:
    return _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _execute_one(
    worktree: Path,
    gate: Gate,
    *,
    default_timeout: float,
) -> GateResult:
    """Execute a single gate, capturing stdout/stderr and runner-side errors."""
    started = _now_iso()
    started_monotonic = time.monotonic()
    timeout = gate.timeout if gate.timeout and gate.timeout > 0 else default_timeout
    env = _build_subprocess_env()
    try:
        proc = subprocess.run(
            list(gate.cmd),
            cwd=str(worktree),
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        duration = time.monotonic() - started_monotonic
        captured_stdout = ""
        captured_stderr = ""
        if exc.stdout:
            captured_stdout = exc.stdout if isinstance(exc.stdout, str) else exc.stdout.decode(
                "utf-8", "replace"
            )
        if exc.stderr:
            captured_stderr = exc.stderr if isinstance(exc.stderr, str) else exc.stderr.decode(
                "utf-8", "replace"
            )
        return GateResult(
            gate=gate,
            exit_code=None,
            stdout_excerpt=_scrub(_truncate(captured_stdout)),
            stderr_excerpt=_scrub(_truncate(captured_stderr)),
            duration_seconds=duration,
            started_at_iso=started,
            error=f"timed out after {timeout:g}s",
        )
    except (FileNotFoundError, PermissionError, OSError) as exc:
        duration = time.monotonic() - started_monotonic
        return GateResult(
            gate=gate,
            exit_code=None,
            stdout_excerpt="",
            stderr_excerpt="",
            duration_seconds=duration,
            started_at_iso=started,
            error=f"{type(exc).__name__}: {exc}",
        )
    except Exception as exc:  # noqa: BLE001 - defensive: never raise
        duration = time.monotonic() - started_monotonic
        return GateResult(
            gate=gate,
            exit_code=None,
            stdout_excerpt="",
            stderr_excerpt="",
            duration_seconds=duration,
            started_at_iso=started,
            error=f"{type(exc).__name__}: {exc}",
        )
    duration = time.monotonic() - started_monotonic
    return GateResult(
        gate=gate,
        exit_code=proc.returncode,
        stdout_excerpt=_scrub(_truncate(proc.stdout or "")),
        stderr_excerpt=_scrub(_truncate(proc.stderr or "")),
        duration_seconds=duration,
        started_at_iso=started,
        error="",
    )


def run_gates(
    worktree: Path,
    gates: Sequence[Gate],
    *,
    artifacts_dir: Path,
    round_number: int,
    mode: str,
    default_timeout: float = DEFAULT_GATE_TIMEOUT_SECONDS,
) -> List[GateResult]:
    """Execute every gate in ``gates`` and persist artifacts.

    Returns the list of ``GateResult`` rows in the same order as
    ``gates``. Persists:
    * ``round-{R}-{mode}-gates.json`` — the entire result list as JSON.
    * ``round-{R}-{mode}-gate-{slug}.txt`` — one human-readable per-gate
      artifact for offline inspection.

    Never raises. A runner-side subprocess failure is recorded with
    ``exit_code=None`` and a non-empty ``error``; the caller is expected
    to treat that as a gate failure via ``gate_results_to_findings``.
    """
    artifacts_dir.mkdir(parents=True, exist_ok=True)
    results: List[GateResult] = []
    for gate in gates:
        result = _execute_one(worktree, gate, default_timeout=default_timeout)
        results.append(result)
        per_gate_path = (
            artifacts_dir
            / f"round-{round_number}-{mode}-gate-{_safe_slug(gate.name)}.txt"
        )
        body = _render_per_gate_body(result)
        per_gate_path.write_text(body, encoding="utf-8")
    manifest = artifacts_dir / f"round-{round_number}-{mode}-gates.json"
    manifest.write_text(
        json.dumps([result.to_dict() for result in results], indent=2),
        encoding="utf-8",
    )
    return results


def _render_per_gate_body(result: GateResult) -> str:
    lines: List[str] = []
    lines.append(f"gate: {result.gate.name}")
    lines.append(f"cmd: {' '.join(result.gate.cmd)}")
    lines.append(f"source: {result.gate.source}")
    lines.append(f"started: {result.started_at_iso}")
    lines.append(f"duration_seconds: {result.duration_seconds:.3f}")
    if result.exit_code is None:
        lines.append("exit_code: <runner-error>")
        lines.append(f"error: {result.error}")
    else:
        lines.append(f"exit_code: {result.exit_code}")
    lines.append("")
    lines.append("---- stdout ----")
    lines.append(result.stdout_excerpt or "")
    lines.append("---- stderr ----")
    lines.append(result.stderr_excerpt or "")
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# Findings adapter
# ---------------------------------------------------------------------------


def _build_evidence(result: GateResult) -> str:
    """Render the short evidence string for the synthetic finding."""
    if result.exit_code is None:
        prefix = f"Runner error: {result.error}"
    else:
        prefix = f"Gate exit_code={result.exit_code}"
    cmd_line = " ".join(result.gate.cmd)
    tail = result.stderr_excerpt or result.stdout_excerpt
    if tail:
        tail = tail.strip()
        if len(tail) > 2000:
            tail = tail[:2000] + "\n[...]"
    body = f"{prefix} for `{cmd_line}` ({result.gate.source})."
    if tail:
        body += f"\nOutput tail:\n{tail}"
    return body


def _build_required_fix(result: GateResult) -> str:
    cmd_line = " ".join(result.gate.cmd)
    base = f"Run `{cmd_line}` locally and address the failure"
    if result.gate.required_fix_hint:
        return f"{base}. {result.gate.required_fix_hint}"
    return base + "."


def _build_finding_message(result: GateResult) -> str:
    if result.exit_code is None:
        return (
            f"Deterministic gate {result.gate.name!r} failed to execute "
            f"({result.error or 'runner error'})."
        )
    return (
        f"Deterministic gate {result.gate.name!r} failed with exit "
        f"code {result.exit_code}."
    )


def gate_results_to_findings(
    results: Sequence[GateResult],
    *,
    round_number: int,
) -> List["object"]:
    """Convert failed ``GateResult`` rows into ``ReviewFinding`` objects.

    Passed gates are skipped. Failed gates (``exit_code != 0`` OR
    ``exit_code is None``) emit one ``ReviewFinding`` each, with
    ``reviewer = f"gate:{gate.name}"`` so the loop's audit trail can
    distinguish synthetic findings from LLM-reviewer findings.
    """
    # Imported here to avoid the circular dependency at module load.
    from .checkup_review_loop import ReviewFinding

    findings: List[ReviewFinding] = []
    for result in results:
        if result.passed:
            continue
        findings.append(
            ReviewFinding(
                severity=result.gate.severity,
                reviewer=f"gate:{result.gate.name}",
                area=result.gate.area,
                evidence=_build_evidence(result),
                finding=_build_finding_message(result),
                required_fix=_build_required_fix(result),
                location=result.gate.source,
                status="open",
                round_number=round_number,
            )
        )
    return findings


__all__ = [
    "DEFAULT_GATE_TIMEOUT_SECONDS",
    "Gate",
    "GateResult",
    "discover_gates",
    "gate_results_to_findings",
    "run_gates",
]
