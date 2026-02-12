"""Tests for Issue #418: Temp directory cleanup on git clone failure."""

import json
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pdd.agentic_change import run_agentic_change


def test_temp_dir_cleaned_up_on_clone_failure(tmp_path: Path):
    """Test temp directory is cleaned up when git clone fails."""
    real_temp_dir = tmp_path / "pdd_test_repo"
    real_temp_dir.mkdir()

    with patch("pdd.agentic_change.shutil.which") as mock_which, \
         patch("pdd.agentic_change.subprocess.run") as mock_subprocess, \
         patch("pdd.agentic_change.tempfile.mkdtemp", return_value=str(real_temp_dir)), \
         patch("pdd.agentic_change.console"), \
         patch("pdd.agentic_change.Path.cwd") as mock_cwd:

        mock_which.return_value = "/usr/bin/gh"
        mock_cwd.return_value.__truediv__.return_value.exists.return_value = False

        issue_data = {
            "title": "Test", "body": "Test", "user": {"login": "test"},
            "comments_url": "https://api.github.com/repos/owner/repo/issues/1/comments"
        }

        def subprocess_side_effect(args, **kwargs):
            cmd = args if isinstance(args, list) else []
            if "api" in cmd and "repos/owner/repo/issues/1" in cmd[2]:
                return MagicMock(returncode=0, stdout=json.dumps(issue_data))
            if "api" in cmd and "comments" in cmd[2]:
                return MagicMock(returncode=0, stdout="[]")
            if "git" in cmd[0] and "remote" in cmd:
                return MagicMock(returncode=1)
            if "repo" in cmd and "clone" in cmd:
                return MagicMock(returncode=1, stderr="fatal: repository not found")
            return MagicMock(returncode=0, stdout="")

        mock_subprocess.side_effect = subprocess_side_effect

        assert real_temp_dir.exists()
        success, msg, _, _, _ = run_agentic_change("https://github.com/owner/repo/issues/1")

        assert success is False
        assert "Failed to clone repository" in msg
        assert not real_temp_dir.exists(), "Temp directory not cleaned up on failure"


def test_temp_dir_cleaned_up_on_subprocess_exception(tmp_path: Path):
    """Test temp directory is cleaned up when subprocess raises exception."""
    real_temp_dir = tmp_path / "pdd_test_exception"
    real_temp_dir.mkdir()

    with patch("pdd.agentic_change.shutil.which", return_value="/usr/bin/gh"), \
         patch("pdd.agentic_change.subprocess.run") as mock_subprocess, \
         patch("pdd.agentic_change.tempfile.mkdtemp", return_value=str(real_temp_dir)), \
         patch("pdd.agentic_change.console"), \
         patch("pdd.agentic_change.Path.cwd") as mock_cwd:

        mock_cwd.return_value.__truediv__.return_value.exists.return_value = False
        issue_data = {
            "title": "Test", "body": "Test", "user": {"login": "test"},
            "comments_url": "https://api.github.com/repos/owner/repo/issues/1/comments"
        }

        def subprocess_side_effect(args, **kwargs):
            cmd = args if isinstance(args, list) else []
            if "api" in cmd and "repos/owner/repo/issues/1" in cmd[2]:
                return MagicMock(returncode=0, stdout=json.dumps(issue_data))
            if "api" in cmd and "comments" in cmd[2]:
                return MagicMock(returncode=0, stdout="[]")
            if "git" in cmd[0] and "remote" in cmd:
                return MagicMock(returncode=1)
            if "repo" in cmd and "clone" in cmd:
                raise OSError("Command not found: gh")
            return MagicMock(returncode=0)

        mock_subprocess.side_effect = subprocess_side_effect

        assert real_temp_dir.exists()
        success, msg, _, _, _ = run_agentic_change("https://github.com/owner/repo/issues/1")

        assert success is False
        assert "Failed to execute clone command" in msg
        assert not real_temp_dir.exists(), "Temp directory not cleaned up on exception"


def test_temp_dir_not_cleaned_up_on_success(tmp_path: Path):
    """Regression test: successful clone should keep temp directory."""
    real_temp_dir = tmp_path / "pdd_test_success"
    real_temp_dir.mkdir()

    with patch("pdd.agentic_change.shutil.which", return_value="/usr/bin/gh"), \
         patch("pdd.agentic_change.subprocess.run") as mock_subprocess, \
         patch("pdd.agentic_change.tempfile.mkdtemp", return_value=str(real_temp_dir)), \
         patch("pdd.agentic_change.run_agentic_change_orchestrator", return_value=(True, "Success", 1.0, "gpt-4", ["file.py"])), \
         patch("pdd.agentic_change.console"), \
         patch("pdd.agentic_change.Path.cwd") as mock_cwd:

        mock_cwd.return_value.__truediv__.return_value.exists.return_value = False
        issue_data = {
            "title": "Test", "body": "Test", "user": {"login": "test"},
            "comments_url": "https://api.github.com/repos/owner/repo/issues/1/comments"
        }

        def subprocess_side_effect(args, **kwargs):
            cmd = args if isinstance(args, list) else []
            if "api" in cmd and "repos/owner/repo/issues/1" in cmd[2]:
                return MagicMock(returncode=0, stdout=json.dumps(issue_data))
            if "api" in cmd and "comments" in cmd[2]:
                return MagicMock(returncode=0, stdout="[]")
            if "git" in cmd[0] and "remote" in cmd:
                return MagicMock(returncode=1)
            if "repo" in cmd and "clone" in cmd:
                return MagicMock(returncode=0, stdout="Cloning...")
            return MagicMock(returncode=0)

        mock_subprocess.side_effect = subprocess_side_effect

        success, msg, _, _, _ = run_agentic_change("https://github.com/owner/repo/issues/1")

        assert success is True
        assert real_temp_dir.exists(), "Successful clone should not cleanup temp directory"
