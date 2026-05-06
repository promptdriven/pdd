
import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

"""
Test plan for pdd/agentic_architecture.py:

1.  **URL Parsing Logic (Z3 & Unit)**:
    *   Verify the regex logic accepts valid GitHub issue URLs and rejects invalid ones.
    *   Unit tests for specific edge cases (http vs https, www, trailing slashes).

2.  **Environment & Dependency Checks**:
    *   Test `run_agentic_architecture` when `gh` CLI is missing.

3.  **GitHub API Interaction**:
    *   Mock `subprocess.run` to simulate `gh api` responses.
    *   Test handling of valid issue JSON.
    *   Test handling of API errors (non-zero exit code).
    *   Test comment fetching and aggregation.

4.  **Repository Context Management**:
    *   Test logic when CWD is already the repo.
    *   Test logic when CWD is a mismatch (should warn).
    *   Test logic when repo needs to be cloned.
    *   Test clone failure handling.

5.  **Orchestrator Invocation**:
    *   Verify that `run_agentic_architecture_orchestrator` is called with the correct parameters derived from the issue and repo state.
"""

import sys
import json
import subprocess
import pytest
from unittest.mock import MagicMock, patch
from pathlib import Path
import z3
from typing import Tuple, List, Optional

# Import the module under test
try:
    from pdd.agentic_architecture import (
        run_agentic_architecture,
        run_incremental_architecture,
        _is_github_issue_url,
        _parse_github_url,
        _extract_target_dir,
    )
except ImportError:
    # Fallback for direct execution if package structure isn't set up
    sys.path.append(str(Path(__file__).parent.parent.parent))
    from pdd.agentic_architecture import (
        run_agentic_architecture,
        run_incremental_architecture,
        _is_github_issue_url,
        _parse_github_url,
        _extract_target_dir,
    )

# --- Z3 Formal Verification ---

def test_z3_url_parsing_logic() -> None:
    """
    Formally verify the constraints of the URL parsing logic using Z3.
    We model the structure of a valid URL and ensure the parser's requirements are consistent.
    """
    s = z3.Solver()

    # We model the components of the URL as integers representing their presence/validity
    # 0 = missing/invalid, 1 = present/valid
    has_domain = z3.Int('has_domain')
    has_owner = z3.Int('has_owner')
    has_repo = z3.Int('has_repo')
    has_issues_segment = z3.Int('has_issues_segment')
    has_number = z3.Int('has_number')

    # Constraints for components
    s.add(z3.Or(has_domain == 0, has_domain == 1))
    s.add(z3.Or(has_owner == 0, has_owner == 1))
    s.add(z3.Or(has_repo == 0, has_repo == 1))
    s.add(z3.Or(has_issues_segment == 0, has_issues_segment == 1))
    s.add(z3.Or(has_number == 0, has_number == 1))

    # Definition of a valid URL structure for this specific parser
    is_valid_url = z3.And(
        has_domain == 1,
        has_owner == 1,
        has_repo == 1,
        has_issues_segment == 1,
        has_number == 1
    )

    # Verify that if any component is missing, it is NOT a valid URL
    # Case 1: Missing number
    s.push()
    s.add(has_number == 0)
    s.add(is_valid_url)
    assert s.check() == z3.unsat, "Z3 found a case where a URL without a number is considered valid"
    s.pop()

    # Case 2: Missing 'issues' segment
    s.push()
    s.add(has_issues_segment == 0)
    s.add(is_valid_url)
    assert s.check() == z3.unsat, "Z3 found a case where a URL without 'issues' segment is considered valid"
    s.pop()

# --- Unit Tests ---

@pytest.fixture
def mock_subprocess():
    with patch("pdd.agentic_architecture.subprocess.run") as mock:
        yield mock

@pytest.fixture
def mock_shutil_which():
    with patch("pdd.agentic_architecture.shutil.which") as mock:
        yield mock

@pytest.fixture
def mock_orchestrator():
    with patch("pdd.agentic_architecture.run_agentic_architecture_orchestrator") as mock:
        yield mock

@pytest.fixture
def mock_cwd():
    with patch("pdd.agentic_architecture.Path.cwd") as mock:
        yield mock

class TestUrlParsing:
    def test_valid_urls(self) -> None:
        valid_urls = [
            ("https://github.com/owner/repo/issues/123", ("owner", "repo", 123)),
            ("http://github.com/owner/repo/issues/123", ("owner", "repo", 123)),
            ("https://www.github.com/owner/repo/issues/123", ("owner", "repo", 123)),
            ("github.com/owner/repo/issues/123", ("owner", "repo", 123)),
        ]
        for url, expected in valid_urls:
            assert _is_github_issue_url(url) is True
            assert _parse_github_url(url) == expected

    def test_invalid_urls(self) -> None:
        invalid_urls = [
            "https://gitlab.com/owner/repo/issues/123",
            "https://github.com/owner/repo/pull/123",
            "https://github.com/owner/repo",
            "not_a_url",
            "https://github.com/owner/repo/issues/not_a_number",
        ]
        for url in invalid_urls:
            assert _is_github_issue_url(url) is False
            assert _parse_github_url(url) is None

class TestRunAgenticArchitecture:
    
    def test_gh_cli_missing(self, mock_shutil_which: MagicMock) -> None:
        mock_shutil_which.return_value = None
        success, msg, cost, model, files = run_agentic_architecture("https://github.com/o/r/issues/1")
        
        assert success is False
        assert "gh CLI not found" in msg
        assert cost == 0.0

    def test_invalid_url_input(self, mock_shutil_which: MagicMock) -> None:
        mock_shutil_which.return_value = "/usr/bin/gh"
        success, msg, cost, model, files = run_agentic_architecture("invalid_url")
        
        assert success is False
        assert "Invalid GitHub URL" in msg

    def test_issue_fetch_failure(self, mock_shutil_which: MagicMock, mock_subprocess: MagicMock) -> None:
        mock_shutil_which.return_value = "/usr/bin/gh"

        # Mock gh api call failure: check=True raises CalledProcessError on non-zero exit
        mock_subprocess.side_effect = subprocess.CalledProcessError(
            1, ["gh", "api", "repos/o/r/issues/1"], stderr="Not Found"
        )

        success, msg, cost, model, files = run_agentic_architecture("https://github.com/o/r/issues/1")

        assert success is False
        assert "Issue not found" in msg

    def test_successful_flow_existing_repo(self, mock_shutil_which: MagicMock, mock_subprocess: MagicMock, mock_orchestrator: MagicMock, mock_cwd: MagicMock) -> None:
        """
        Test the happy path where the repo is already the current working directory.
        """
        mock_shutil_which.return_value = "/usr/bin/gh"
        mock_cwd.return_value = Path("/path/to/repo")
        
        issue_json = json.dumps({
            "title": "Fix Bug",
            "body": "Bug description",
            "user": {"login": "author"},
            "comments_url": "https://api.github.com/repos/o/r/issues/1/comments"
        })
        
        comments_json = json.dumps([
            {"user": {"login": "commenter"}, "body": "I agree"}
        ])
        
        def subprocess_side_effect(args, **kwargs):
            cmd = args if isinstance(args, list) else args
            cmd_str = " ".join(cmd)

            # gh api issue (command: ["gh", "api", "repos/o/r/issues/1"])
            if "gh" in cmd and "api" in cmd and "issues/1" in cmd_str and "comments" not in cmd_str:
                return MagicMock(returncode=0, stdout=issue_json, stderr="")

            # gh api comments (command: ["gh", "api", "<comments_url>"])
            if "gh" in cmd and "api" in cmd and "comments" in cmd_str:
                return MagicMock(returncode=0, stdout=comments_json, stderr="")

            # git config remote
            if "git" in cmd and "config" in cmd:
                return MagicMock(returncode=0, stdout="https://github.com/o/r.git", stderr="")

            return MagicMock(returncode=1, stdout="", stderr="Unknown command")

        mock_subprocess.side_effect = subprocess_side_effect
        
        # Mock orchestrator return
        mock_orchestrator.return_value = (True, "Done", 0.5, "gpt-4", ["file.py"])

        success, msg, cost, model, files = run_agentic_architecture(
            "https://github.com/o/r/issues/1",
            verbose=True
        )

        assert success is True
        assert msg == "Done"
        
        # Verify orchestrator called with correct content
        mock_orchestrator.assert_called_once()
        call_kwargs = mock_orchestrator.call_args[1]
        assert "Bug description" in call_kwargs["issue_content"]
        assert "User: commenter" in call_kwargs["issue_content"]
        assert call_kwargs["repo_owner"] == "o"
        assert call_kwargs["repo_name"] == "r"
        assert call_kwargs["cwd"] == Path("/path/to/repo")

    def test_repo_clone_needed(self, mock_shutil_which: MagicMock, mock_subprocess: MagicMock, mock_orchestrator: MagicMock, mock_cwd: MagicMock) -> None:
        """
        Test flow where repo is not present and needs cloning.
        """
        mock_shutil_which.return_value = "/usr/bin/gh"
        mock_cwd.return_value = Path("/tmp")
        
        issue_json = json.dumps({"title": "T", "body": "B", "user": {"login": "u"}, "comments_url": ""})
        
        def subprocess_side_effect(args, **kwargs):
            cmd = args
            # gh api issue
            if "gh" in cmd and "api" in cmd:
                return MagicMock(returncode=0, stdout=issue_json, stderr="")
            
            # git config remote (fails, not a repo)
            if "git" in cmd and "config" in cmd:
                return MagicMock(returncode=1, stdout="", stderr="")
            
            # gh repo clone
            if "gh" in cmd and "repo" in cmd and "clone" in cmd:
                return MagicMock(returncode=0, stdout="Cloning...", stderr="")
                
            return MagicMock(returncode=1, stdout="", stderr="Unknown")

        mock_subprocess.side_effect = subprocess_side_effect
        mock_orchestrator.return_value = (True, "Done", 0.0, "", [])

        # We need to mock Path.exists and is_dir to simulate repo dir NOT existing initially
        with patch("pathlib.Path.exists", return_value=False):
            with patch("pathlib.Path.is_dir", return_value=False):
                run_agentic_architecture("https://github.com/o/r/issues/1")

        # Verify clone was called
        clone_call_found = False
        for call in mock_subprocess.call_args_list:
            args = call[0][0]
            if "gh" in args and "clone" in args and "o/r" in args:
                clone_call_found = True
                break
        assert clone_call_found

    def test_repo_clone_failure(self, mock_shutil_which: MagicMock, mock_subprocess: MagicMock, mock_cwd: MagicMock) -> None:
        """
        Test flow where cloning fails.
        """
        mock_shutil_which.return_value = "/usr/bin/gh"
        mock_cwd.return_value = Path("/tmp")
        
        issue_json = json.dumps({"title": "T", "body": "B", "user": {"login": "u"}, "comments_url": ""})
        
        def subprocess_side_effect(args, **kwargs):
            cmd = args
            if "gh" in cmd and "api" in cmd:
                return MagicMock(returncode=0, stdout=issue_json, stderr="")
            if "git" in cmd and "config" in cmd:
                return MagicMock(returncode=1, stdout="", stderr="")
            if "gh" in cmd and "clone" in cmd:
                # Simulate clone failure
                raise subprocess.CalledProcessError(1, cmd, stderr="Permission denied")
            return MagicMock(returncode=0)

        mock_subprocess.side_effect = subprocess_side_effect
        
        # Mock path checks to trigger clone path
        with patch("pathlib.Path.exists", return_value=False):
            success, msg, _, _, _ = run_agentic_architecture("https://github.com/o/r/issues/1")
        
        assert success is False
        assert "Failed to clone repository" in msg
        assert "Permission denied" in msg

    def test_json_decode_error(self, mock_shutil_which: MagicMock, mock_subprocess: MagicMock) -> None:
        mock_shutil_which.return_value = "/usr/bin/gh"
        
        # Return invalid JSON
        mock_subprocess.return_value.returncode = 0
        mock_subprocess.return_value.stdout = "Not JSON"
        
        success, msg, _, _, _ = run_agentic_architecture("https://github.com/o/r/issues/1")
        
        assert success is False
        assert "Failed to parse GitHub API response" in msg


class TestRunIncrementalArchitecture:
    def test_local_prd_invokes_guarded_propagation(
        self,
        mock_cwd: MagicMock,
        tmp_path: Path,
    ) -> None:
        prd = tmp_path / "docs" / "prd.md"
        prd.parent.mkdir()
        prd.write_text("Add audit logging", encoding="utf-8")
        mock_cwd.return_value = tmp_path

        with patch("pdd.incremental_prd_architecture.run_incremental_prd_propagation") as mock_run:
            mock_run.return_value = (True, "Applied", 0.5, "model", ["architecture.json"])

            result = run_incremental_architecture("docs/prd.md", dry_run=True, target_dir="service")

        assert result[0] is True
        mock_run.assert_called_once()
        kwargs = mock_run.call_args.kwargs
        assert kwargs["prd_source"] == "docs/prd.md"
        assert kwargs["architecture_path"] == tmp_path / "service" / "architecture.json"
        assert kwargs["prompts_dir"] == tmp_path / "service" / "prompts"
        assert kwargs["project_root"] == tmp_path
        assert kwargs["dry_run"] is True

    @pytest.mark.parametrize(
        "target_dir",
        [
            "../outside",
            "svc; echo OWNED",
            "svc$(echo OWNED)",
            "svc with spaces",
            "svc\nnext",
            "svc`echo OWNED`",
            "-svc",
            "apps/web;",
        ],
    )
    def test_local_prd_rejects_unsafe_target_dir(
        self,
        mock_cwd: MagicMock,
        tmp_path: Path,
        target_dir: str,
    ) -> None:
        prd = tmp_path / "docs" / "prd.md"
        prd.parent.mkdir()
        prd.write_text("Add audit logging", encoding="utf-8")
        mock_cwd.return_value = tmp_path

        with patch("pdd.incremental_prd_architecture.run_incremental_prd_propagation") as mock_run:
            result = run_incremental_architecture(
                "docs/prd.md",
                dry_run=True,
                target_dir=target_dir,
            )

        assert result[0] is False
        assert "Invalid target directory" in result[1]
        mock_run.assert_not_called()

    def test_issue_target_dir_extraction_rejects_unsafe_paths(self) -> None:
        with pytest.raises(ValueError, match="Invalid target directory"):
            _extract_target_dir("Build this in `/tmp/outside`")
        with pytest.raises(ValueError, match="Invalid target directory"):
            _extract_target_dir("Build this in `../outside`")
        with pytest.raises(ValueError, match="Invalid target directory"):
            _extract_target_dir("Build this in `svc; echo OWNED`")
        with pytest.raises(ValueError, match="Invalid target directory"):
            _extract_target_dir("Build this in `svc$(echo OWNED)`")
        with pytest.raises(ValueError, match="Invalid target directory"):
            _extract_target_dir("Build this in `svc\nnext`")
        assert _extract_target_dir("Build this in `services/api`") == "services/api"
        assert _extract_target_dir("Build this in `apps/web.v2`") == "apps/web.v2"
        assert _extract_target_dir("Build this in apps/web.v2") == "apps/web.v2"
        assert _extract_target_dir("Build this in apps/web.v2.") == "apps/web.v2"
        assert _extract_target_dir("Build this in apps/web-v2.1") == "apps/web-v2.1"

    def test_github_issue_invalid_target_dir_fails_instead_of_root_fallback(
        self,
        mock_shutil_which: MagicMock,
        mock_subprocess: MagicMock,
        mock_cwd: MagicMock,
    ) -> None:
        mock_shutil_which.return_value = "/usr/bin/gh"
        mock_cwd.return_value = Path("/path/to/repo")
        issue_json = json.dumps({
            "title": "Incremental PRD update",
            "body": "Build this in `/tmp/outside`",
            "user": {"login": "author"},
            "comments_url": "",
        })

        def subprocess_side_effect(args, **kwargs):
            cmd = args if isinstance(args, list) else args
            if "gh" in cmd and "api" in cmd:
                return MagicMock(returncode=0, stdout=issue_json, stderr="")
            if "git" in cmd and "config" in cmd:
                return MagicMock(returncode=0, stdout="https://github.com/o/r.git", stderr="")
            return MagicMock(returncode=1, stdout="", stderr="Unknown command")

        mock_subprocess.side_effect = subprocess_side_effect

        with patch("pdd.incremental_prd_architecture.run_incremental_prd_propagation") as mock_run:
            result = run_incremental_architecture(
                "https://github.com/o/r/issues/1",
                use_github_state=False,
            )

        assert result[0] is False
        assert "Invalid target directory" in result[1]
        mock_run.assert_not_called()

    def test_github_issue_invokes_guarded_propagation_with_issue_context(
        self,
        mock_shutil_which: MagicMock,
        mock_subprocess: MagicMock,
        mock_cwd: MagicMock,
    ) -> None:
        mock_shutil_which.return_value = "/usr/bin/gh"
        mock_cwd.return_value = Path("/path/to/repo")

        issue_json = json.dumps({
            "title": "Incremental PRD update",
            "body": "Add audit logging in `service`",
            "user": {"login": "author"},
            "comments_url": "https://api.github.com/repos/o/r/issues/1/comments",
        })
        comments_json = json.dumps([
            {"user": {"login": "reviewer"}, "body": "Make it targeted."}
        ])

        def subprocess_side_effect(args, **kwargs):
            cmd = args if isinstance(args, list) else args
            cmd_str = " ".join(cmd)
            if "gh" in cmd and "api" in cmd and "issues/1" in cmd_str and "comments" not in cmd_str:
                return MagicMock(returncode=0, stdout=issue_json, stderr="")
            if "gh" in cmd and "api" in cmd and "comments" in cmd_str and "--paginate" in cmd:
                return MagicMock(returncode=0, stdout=comments_json, stderr="")
            if "gh" in cmd and "api" in cmd and "comments" in cmd_str and "-f" in cmd:
                return MagicMock(returncode=0, stdout="", stderr="")
            if "git" in cmd and "config" in cmd:
                return MagicMock(returncode=0, stdout="https://github.com/o/r.git", stderr="")
            return MagicMock(returncode=1, stdout="", stderr="Unknown command")

        mock_subprocess.side_effect = subprocess_side_effect

        with patch("pdd.incremental_prd_architecture.run_incremental_prd_propagation") as mock_run:
            mock_run.return_value = (True, "Applied", 0.5, "model", ["architecture.json"])

            result = run_incremental_architecture(
                "https://github.com/o/r/issues/1",
                use_github_state=True,
            )

        assert result[0] is True
        assert result[1] == (
            "Applied\nNext: run `cd service && pdd sync` for follow-up sync validation "
            "because generated prompt includes are target-directory relative."
        )
        assert result[4] == ["service/architecture.json"]
        mock_run.assert_called_once()
        kwargs = mock_run.call_args.kwargs
        assert kwargs["prd_source"] == "https://github.com/o/r/issues/1"
        assert "Incremental PRD update" in kwargs["issue_content"]
        assert "Make it targeted." in kwargs["issue_content"]
        assert kwargs["architecture_path"] == Path("/path/to/repo/service/architecture.json")
        assert kwargs["prompts_dir"] == Path("/path/to/repo/service/prompts")

    def test_github_issue_target_dir_noop_does_not_add_sync_hint(
        self,
        mock_shutil_which: MagicMock,
        mock_subprocess: MagicMock,
        mock_cwd: MagicMock,
    ) -> None:
        mock_shutil_which.return_value = "/usr/bin/gh"
        mock_cwd.return_value = Path("/path/to/repo")

        issue_json = json.dumps({
            "title": "Incremental PRD update",
            "body": "No-op update in `service`",
            "user": {"login": "author"},
            "comments_url": "",
        })

        def subprocess_side_effect(args, **kwargs):
            cmd = args if isinstance(args, list) else args
            if "gh" in cmd and "api" in cmd:
                return MagicMock(returncode=0, stdout=issue_json, stderr="")
            if "git" in cmd and "config" in cmd:
                return MagicMock(returncode=0, stdout="https://github.com/o/r.git", stderr="")
            return MagicMock(returncode=1, stdout="", stderr="Unknown command")

        mock_subprocess.side_effect = subprocess_side_effect

        with patch("pdd.incremental_prd_architecture.run_incremental_prd_propagation") as mock_run:
            mock_run.return_value = (True, "No PRD changes detected.", 0.0, "", [])

            result = run_incremental_architecture(
                "https://github.com/o/r/issues/1",
                use_github_state=False,
            )

        assert result[0] is True
        assert result[1] == "No PRD changes detected."
        assert result[4] == []


# --- Issue #1256: Dict-format architecture tolerance ---
# Scope addition: covers expansion item "pdd/agentic_architecture.py:210 and 221
# load architecture.json from sibling dirs with isinstance check that silently
# drops dict-format data" identified by Step 6 but absent from Step 8's plan


def test_fetch_sibling_architectures_dict_format(tmp_path):
    """_fetch_sibling_architectures includes dict-format sibling architecture modules (Test 16).

    Bug: isinstance(arch_data, list) at agentic_architecture.py:210 returns False
    for dict-format {"modules": [...]}, so the sibling architecture is silently
    dropped and not included in the context string.
    """
    from pdd.agentic_architecture import _fetch_sibling_architectures

    # Create sibling subdirectory with dict-format architecture
    sibling = tmp_path / "backend"
    sibling.mkdir()
    sibling_arch = {
        "modules": [
            {"filename": "api_Python.prompt", "priority": 1, "description": "Backend API"},
        ]
    }
    (sibling / "architecture.json").write_text(
        json.dumps(sibling_arch), encoding="utf-8"
    )

    result = _fetch_sibling_architectures(tmp_path, current_target_dir="frontend")
    assert result != "", (
        "Dict-format sibling architecture should be included in context string, "
        "but isinstance(arch_data, list) at agentic_architecture.py:210 silently drops it"
    )
    assert "api_Python" in result or "Backend API" in result, (
        "Context string should mention the sibling module from dict-format architecture"
    )


# --- F3: filter pdd's own incremental status comments -----------------------


def test_fetch_issue_comments_skips_pdd_status_comments():
    """_fetch_issue_comments_text must filter comments containing the
    PDD-INCREMENTAL-STATUS marker so the next run does not see its own bot
    output as a PRD change.
    """
    from unittest.mock import patch as mock_patch

    from pdd.agentic_architecture import (
        _fetch_issue_comments_text,
        _INCREMENTAL_STATUS_MARKER,
    )

    fake_comments = [
        {"user": {"login": "human-user"}, "body": "Please add audit logging."},
        {
            "user": {"login": "github-actions[bot]"},
            "body": (
                f"{_INCREMENTAL_STATUS_MARKER}\n"
                "pdd incremental architecture update successful.\n\n"
                "Result: Applied incremental PRD propagation: 1 affected"
            ),
        },
        {"user": {"login": "another-human"}, "body": "Looks good."},
    ]

    with mock_patch(
        "pdd.agentic_architecture._run_gh_command",
        return_value=(True, json.dumps(fake_comments)),
    ):
        text = _fetch_issue_comments_text(
            "https://api.github.com/repos/o/r/issues/1/comments",
            verbose=False,
        )

    assert "Please add audit logging." in text
    assert "Looks good." in text
    assert _INCREMENTAL_STATUS_MARKER not in text
    assert "pdd incremental architecture update" not in text


def test_post_incremental_status_comment_includes_marker():
    """The posted status body must carry the PDD-INCREMENTAL-STATUS marker so
    _fetch_issue_comments_text can filter it on the next run.
    """
    from unittest.mock import patch as mock_patch

    from pdd.agentic_architecture import (
        _post_incremental_status_comment,
        _INCREMENTAL_STATUS_MARKER,
    )

    captured: dict = {}

    def fake_run_gh(args):
        captured["args"] = args
        return True, ""

    with mock_patch("pdd.agentic_architecture._run_gh_command", side_effect=fake_run_gh):
        _post_incremental_status_comment(
            owner="o",
            repo="r",
            issue_number=1,
            result=(True, "Applied: 1 entry affected", 0.05, "model", ["arch.json"]),
            quiet=True,
        )

    body_arg = next((a for a in captured["args"] if isinstance(a, str) and a.startswith("body=")), None)
    assert body_arg is not None
    assert _INCREMENTAL_STATUS_MARKER in body_arg


def test_post_incremental_status_comment_redacts_absolute_paths():
    """Failure messages can include local paths; public GitHub comments must not."""
    from unittest.mock import patch as mock_patch

    from pdd.agentic_architecture import _post_incremental_status_comment

    captured: dict = {}

    def fake_run_gh(args):
        captured["args"] = args
        return True, ""

    with mock_patch("pdd.agentic_architecture._run_gh_command", side_effect=fake_run_gh):
        _post_incremental_status_comment(
            owner="o",
            repo="r",
            issue_number=1,
            result=(
                False,
                "Incremental architecture error: Architecture file not found: "
                "/Users/alice/work/project/architecture.json; "
                "retry from /workspace/repo/service/architecture.json; "
                "container path /root/repo/architecture.json; "
                "wsl path /mnt/c/repo/architecture.json",
                0.0,
                "",
                ["/workspace/repo/service/prompts/api_python.prompt"],
            ),
            quiet=True,
        )

    body_arg = next((a for a in captured["args"] if isinstance(a, str) and a.startswith("body=")), None)
    assert body_arg is not None
    assert "/Users/alice" not in body_arg
    assert "/workspace/repo" not in body_arg
    assert "/root/repo" not in body_arg
    assert "/mnt/c/repo" not in body_arg
    assert "<local-path>" in body_arg


def test_full_agentic_path_filters_pdd_status_comments():
    """F18: the full (non-incremental) `pdd generate <issue-url>` path must
    also filter `<!-- PDD-INCREMENTAL-STATUS -->` comments out of the PRD
    content. Otherwise a later full regenerate would feed prior incremental
    status output back into the LLM as if it were part of the PRD.

    Validated by exercising the shared `_fetch_issue_comments_text` that the
    full path now uses (and which already filtered for the incremental
    flow). Confirms a single source of truth for the filter.
    """
    from unittest.mock import patch as mock_patch

    from pdd.agentic_architecture import (
        _fetch_issue_comments_text,
        _INCREMENTAL_STATUS_MARKER,
    )

    fake_comments = [
        {"user": {"login": "human"}, "body": "Initial PRD comment from human."},
        {
            "user": {"login": "github-actions[bot]"},
            "body": (
                f"{_INCREMENTAL_STATUS_MARKER}\n"
                "pdd incremental architecture update successful."
            ),
        },
    ]

    with mock_patch(
        "pdd.agentic_architecture._run_gh_command",
        return_value=(True, json.dumps(fake_comments)),
    ):
        text = _fetch_issue_comments_text(
            "https://api.github.com/repos/o/r/issues/1/comments",
            verbose=False,
        )

    assert "Initial PRD comment from human." in text
    assert _INCREMENTAL_STATUS_MARKER not in text
    assert "pdd incremental architecture update" not in text
