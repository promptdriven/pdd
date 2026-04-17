"""Tests for pdd.agentic_split module (CLI wrapper).

Test Plan:
1. run_agentic_split — file not found
2. run_agentic_split — unsupported file extension
3. run_agentic_split — not inside git repo
4. run_agentic_split — no prompt file (warning only, continues)
5. run_agentic_split — no test file (warning only, continues)
6. run_agentic_split — successful delegation to orchestrator
7. run_agentic_split — orchestrator exception caught
8. run_agentic_split — quiet mode suppresses warnings
"""
from __future__ import annotations

from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pdd.agentic_split import run_agentic_split

MODULE = "pdd.agentic_split"


class TestFileNotFound:
    def test_nonexistent_file(self):
        ok, msg, cost, model, files = run_agentic_split(
            "/nonexistent/path/to/file.py", quiet=True,
        )
        assert ok is False
        assert "does not exist" in msg
        assert cost == 0.0

    def test_directory_not_file(self, tmp_path):
        ok, msg, cost, model, files = run_agentic_split(
            str(tmp_path), quiet=True,
        )
        assert ok is False
        assert "not a file" in msg


class TestUnsupportedExtension:
    def test_unknown_extension(self, tmp_path):
        f = tmp_path / "data.xyz"
        f.write_text("content")
        with patch(f"{MODULE}.get_language", return_value=""):
            ok, msg, cost, model, files = run_agentic_split(
                str(f), quiet=True,
            )
            assert ok is False
            assert "Unsupported" in msg


class TestNotGitRepo:
    def test_no_git_root(self, tmp_path):
        f = tmp_path / "mod.py"
        f.write_text("x = 1")
        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.get_git_root", return_value=None):
            ok, msg, cost, model, files = run_agentic_split(
                str(f), quiet=True,
            )
            assert ok is False
            assert "git" in msg.lower()


class TestPromptDiscovery:
    def test_finds_prompt_in_extensions_path(self, tmp_path):
        """Prompt at extensions/foo/prompts/.../X.prompt should be found (no warning)."""
        f = tmp_path / "mod.py"
        f.write_text("x = 1")
        # Create extensions/foo/prompts/src/mod_Python.prompt (capitalized)
        prompts_path = tmp_path / "extensions" / "foo" / "prompts" / "src"
        prompts_path.mkdir(parents=True)
        (prompts_path / "mod_Python.prompt").write_text("prompt content")

        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.run_agentic_split_orchestrator",
                   return_value=(True, "ok", 0.5, "model", [])), \
             patch(f"{MODULE}.console") as mock_console:
            run_agentic_split(str(f), quiet=False)
            # Should NOT print a prompt warning
            prompt_warnings = [
                c for c in mock_console.print.call_args_list
                if "Warning" in str(c) and "prompt" in str(c).lower()
            ]
            assert len(prompt_warnings) == 0, f"Unexpected warnings: {prompt_warnings}"


class TestPromptFileWarning:
    def test_no_prompt_prints_warning(self, tmp_path, capsys):
        f = tmp_path / "mod.py"
        f.write_text("x = 1")
        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.run_agentic_split_orchestrator",
                   return_value=(True, "ok", 0.5, "model", [])), \
             patch(f"{MODULE}.console") as mock_console:
            run_agentic_split(str(f), quiet=False)
            # Should have printed a warning about missing prompt
            warning_calls = [
                c for c in mock_console.print.call_args_list
                if "Warning" in str(c) and "prompt" in str(c).lower()
            ]
            assert len(warning_calls) >= 1


class TestTestFileWarning:
    def test_no_test_prints_warning(self, tmp_path, capsys):
        f = tmp_path / "mod.py"
        f.write_text("x = 1")
        # Create prompt so only test warning fires
        prompts = tmp_path / "prompts"
        prompts.mkdir()
        (prompts / "mod_Python.prompt").write_text("prompt")
        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.run_agentic_split_orchestrator",
                   return_value=(True, "ok", 0.5, "model", [])), \
             patch(f"{MODULE}.console") as mock_console:
            run_agentic_split(str(f), quiet=False)
            warning_calls = [
                c for c in mock_console.print.call_args_list
                if "Warning" in str(c) and "test" in str(c).lower()
            ]
            assert len(warning_calls) >= 1


class TestSuccessfulDelegation:
    def test_delegates_to_orchestrator(self, tmp_path):
        f = tmp_path / "mod.py"
        f.write_text("x = 1")
        expected = (True, "Split complete", 1.5, "model-x", ["a.py"])
        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.run_agentic_split_orchestrator",
                   return_value=expected) as mock_orch:
            ok, msg, cost, model, files = run_agentic_split(
                str(f), quiet=True, diagnose_only=True,
            )
            assert ok is True
            assert msg == "Split complete"
            assert cost == 1.5
            # Verify orchestrator was called with correct args
            call_kwargs = mock_orch.call_args[1]
            assert call_kwargs["diagnose_only"] is True
            assert call_kwargs["cwd"] == tmp_path


class TestOrchestratorException:
    def test_exception_caught(self, tmp_path):
        f = tmp_path / "mod.py"
        f.write_text("x = 1")
        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.run_agentic_split_orchestrator",
                   side_effect=RuntimeError("boom")):
            ok, msg, cost, model, files = run_agentic_split(
                str(f), quiet=True,
            )
            assert ok is False
            assert "boom" in msg
            assert cost == 0.0


class TestQuietMode:
    def test_quiet_suppresses_warnings(self, tmp_path):
        f = tmp_path / "mod.py"
        f.write_text("x = 1")
        with patch(f"{MODULE}.get_language", return_value="Python"), \
             patch(f"{MODULE}.get_git_root", return_value=tmp_path), \
             patch(f"{MODULE}.run_agentic_split_orchestrator",
                   return_value=(True, "ok", 0.5, "model", [])), \
             patch(f"{MODULE}.console") as mock_console:
            run_agentic_split(str(f), quiet=True)
            mock_console.print.assert_not_called()
