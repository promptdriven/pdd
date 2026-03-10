"""E2E tests for issue #797: Independent verification skips TypeScript test files.

These tests exercise the full run_agentic_e2e_fix_orchestrator flow WITHOUT
mocking _extract_test_files or _verify_tests_independently. This verifies
the bug at the system level: when only TypeScript test files exist and the
LLM claims ALL_TESTS_PASS, the orchestrator should NOT blindly trust the
claim — it should find and attempt to verify those TypeScript test files.

Bug: _extract_test_files only recognizes .py files, so TypeScript test files
are invisible, causing the orchestrator to print "No test files found for
independent verification. Trusting LLM output." and exit successfully.
"""
import subprocess
from pathlib import Path
from typing import Dict, Optional

import pytest
from unittest.mock import patch, MagicMock

from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator


@pytest.fixture
def e2e_797_mock_dependencies(tmp_path):
    """Mocks external dependencies but NOT _extract_test_files or _verify_tests_independently.

    This is the key difference from the unit tests in TestIssue797TypeScriptTestFiles:
    we let the real extraction and verification code run so we can observe the
    system-level behavior of the bug.
    """
    mock_proc = MagicMock(returncode=0, stdout="PASS", stderr="")
    with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_e2e_fix_orchestrator.console") as mock_console, \
         patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state") as mock_load_state, \
         patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state") as mock_save_state, \
         patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state") as mock_clear_state, \
         patch("pdd.agentic_e2e_fix_orchestrator._get_file_hashes") as mock_hashes, \
         patch("pdd.agentic_e2e_fix_orchestrator._commit_and_push") as mock_commit, \
         patch("pdd.agentic_e2e_fix_orchestrator.get_test_command_for_file", return_value="npx jest {file}") as mock_get_cmd, \
         patch("subprocess.run", return_value=mock_proc) as mock_subproc:

        mock_run.return_value = (True, "Step output", 0.1, "gpt-4")
        mock_load.return_value = "Prompt for {issue_number}"
        mock_load_state.return_value = (None, None)
        mock_save_state.return_value = None
        mock_hashes.return_value = {}
        mock_commit.return_value = (True, "No changes to commit")

        yield mock_run, mock_load, mock_console


@pytest.fixture
def e2e_797_default_args(tmp_path):
    """Default orchestrator arguments for issue #797 tests."""
    return {
        "issue_url": "http://github.com/owner/repo/issues/797",
        "issue_content": "Bug in WaitlistPending auto-refresh",
        "repo_owner": "owner",
        "repo_name": "repo",
        "issue_number": 797,
        "issue_author": "user",
        "issue_title": "TypeScript test verification bug",
        "cwd": tmp_path,
        "verbose": False,
        "quiet": True,
        "resume": False,
        "use_github_state": False,
    }


class TestE2EIssue797TypeScriptVerification:
    """E2E tests reproducing the exact scenario from issue #797.

    The LLM claims ALL_TESTS_PASS but only TypeScript test files exist.
    The orchestrator should NOT exit successfully when it cannot verify
    non-Python test files.
    """

    def test_step2_all_tests_pass_with_only_tsx_changed_files_should_not_trust_blindly(
        self, e2e_797_mock_dependencies, e2e_797_default_args, tmp_path
    ):
        """Full orchestrator run: LLM claims ALL_TESTS_PASS at Step 2 with .test.tsx in changed_files.

        Reproduces the core issue #797 scenario:
        1. LLM returns ALL_TESTS_PASS at Step 2
        2. The only test file is a .test.tsx (TypeScript/Jest)
        3. _extract_test_files (real, not mocked) should find the .tsx file
        4. Orchestrator should NOT blindly trust the LLM claim

        Bug behavior: _extract_test_files returns [] because of .py filter,
        orchestrator prints "No test files found" and exits with success=True.
        """
        mock_run, _, mock_console = e2e_797_mock_dependencies

        # Create a TypeScript test file on disk (simulating LLM creating it)
        test_dir = tmp_path / "frontend" / "src" / "components" / "__test__"
        test_dir.mkdir(parents=True)
        tsx_test = test_dir / "WaitlistPending.test.tsx"
        tsx_test.write_text("test('renders correctly', () => { expect(true).toBe(true); });")

        # LLM output includes the .tsx file in changed_files-like references
        # and claims ALL_TESTS_PASS at Step 2
        call_count = 0

        def side_effect(*args, **kwargs):
            nonlocal call_count
            call_count += 1
            label = kwargs.get("label", "")
            if "step2" in label:
                return (
                    True,
                    "ALL_TESTS_PASS - all tests verified\n"
                    "Changed: frontend/src/components/__test__/WaitlistPending.test.tsx",
                    0.1,
                    "gpt-4",
                )
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect
        e2e_797_default_args["max_cycles"] = 1

        # The issue_content references the TypeScript test file
        e2e_797_default_args["issue_content"] = (
            "Bug in WaitlistPending auto-refresh.\n"
            "Test file: frontend/src/components/__test__/WaitlistPending.test.tsx\n"
            "E2E_FILES_CREATED: frontend/src/components/__test__/WaitlistPending.test.tsx"
        )

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            **e2e_797_default_args
        )

        # BUG: The orchestrator exits with success=True because _extract_test_files
        # returns [] (no .py files found), triggering the "Trusting LLM output" path.
        # EXPECTED: The orchestrator should find the .tsx test file and attempt
        # verification, or at minimum NOT claim verified success.
        assert success is False or "no independent verification" not in msg.lower(), (
            "Orchestrator blindly trusted ALL_TESTS_PASS without verifying TypeScript "
            "test files — the exact bug from issue #797. _extract_test_files should "
            "recognize .test.tsx files."
        )

    def test_step9_all_tests_pass_with_only_spec_ts_should_not_trust_blindly(
        self, e2e_797_mock_dependencies, e2e_797_default_args, tmp_path
    ):
        """Full orchestrator run: LLM claims ALL_TESTS_PASS at Step 9 with .spec.ts files.

        Reproduces issue #797 at the Step 9 exit point (the other ALL_TESTS_PASS check).
        """
        mock_run, _, mock_console = e2e_797_mock_dependencies

        # Create a Playwright spec file on disk
        test_dir = tmp_path / "frontend" / "e2e" / "tests" / "waitlist-pending"
        test_dir.mkdir(parents=True)
        spec_file = test_dir / "auto-refresh.spec.ts"
        spec_file.write_text("test('auto-refresh works', async ({ page }) => {});")

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step9" in label:
                return (
                    True,
                    "ALL_TESTS_PASS - verified all Playwright tests pass",
                    0.1,
                    "gpt-4",
                )
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect
        e2e_797_default_args["max_cycles"] = 1

        e2e_797_default_args["issue_content"] = (
            "Bug in WaitlistPending auto-refresh.\n"
            "E2E_FILES_CREATED: frontend/e2e/tests/waitlist-pending/auto-refresh.spec.ts"
        )

        success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
            **e2e_797_default_args
        )

        # BUG: Orchestrator exits with success=True at Step 9 because
        # _extract_test_files finds no .py test files. It prints the
        # "ALL_TESTS_PASS detected in Step 9" message without verification.
        # After fix, it should find the .spec.ts file and attempt verification.
        all_print_calls = [
            str(call) for call in mock_console.print.call_args_list
        ]
        verified_messages = [
            c for c in all_print_calls if "verified" in c.lower()
        ]
        unverified_step9 = [
            c for c in all_print_calls
            if "ALL_TESTS_PASS detected in Step 9" in c
        ]
        assert len(unverified_step9) == 0, (
            "Orchestrator accepted ALL_TESTS_PASS at Step 9 without independent "
            "verification even though .spec.ts test files exist — issue #797 bug.\n"
            f"Console output: {all_print_calls}"
        )

    def test_step2_tsx_disk_change_detection_triggers_verification(
        self, e2e_797_default_args, tmp_path
    ):
        """Full orchestrator: TypeScript test file created on disk should be detected.

        Tests the disk-change detection path (line 205) through the full orchestrator.
        Even without markers or changed_files, a .test.tsx file created during the
        workflow should be found by _extract_test_files via hash comparison.

        This test does NOT use the shared fixture because it needs _get_file_hashes
        to return real values on the second call (simulating a file created during
        the workflow).
        """
        import hashlib

        # Initialize git repo (needed for disk-change detection)
        subprocess.run(["git", "init"], cwd=tmp_path, capture_output=True)
        subprocess.run(
            ["git", "commit", "--allow-empty", "-m", "init"],
            cwd=tmp_path,
            capture_output=True,
        )

        # Create a .test.tsx file that should be detected as "new during workflow"
        test_dir = tmp_path / "src" / "__test__"
        test_dir.mkdir(parents=True)
        tsx_content = "test('component renders', () => { expect(1).toBe(1); });"
        (test_dir / "Component.test.tsx").write_text(tsx_content)
        tsx_hash = hashlib.md5(tsx_content.encode()).hexdigest()

        call_count = [0]

        def mock_get_file_hashes(cwd):
            """First call returns {} (initial snapshot). Subsequent calls return the tsx file."""
            call_count[0] += 1
            if call_count[0] == 1:
                return {}  # Initial snapshot: no files
            return {"src/__test__/Component.test.tsx": tsx_hash}

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step2" in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_proc = MagicMock(returncode=0, stdout="PASS", stderr="")
        with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template") as mock_load, \
             patch("pdd.agentic_e2e_fix_orchestrator.console") as mock_console, \
             patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state") as mock_load_state, \
             patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state") as mock_save_state, \
             patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state") as mock_clear_state, \
             patch("pdd.agentic_e2e_fix_orchestrator._get_file_hashes") as mock_hashes, \
             patch("pdd.agentic_e2e_fix_orchestrator._commit_and_push") as mock_commit, \
             patch("pdd.agentic_e2e_fix_orchestrator.get_test_command_for_file", return_value="npx jest {file}"), \
             patch("subprocess.run", return_value=mock_proc):

            mock_run.side_effect = side_effect
            mock_load.return_value = "Prompt for {issue_number}"
            mock_load_state.return_value = (None, None)
            mock_save_state.return_value = None
            mock_hashes.side_effect = mock_get_file_hashes
            mock_commit.return_value = (True, "No changes to commit")

            e2e_797_default_args["max_cycles"] = 1
            e2e_797_default_args["issue_content"] = "Bug description with no file markers"

            success, msg, cost, model, files = run_agentic_e2e_fix_orchestrator(
                **e2e_797_default_args
            )

        # BUG: disk-change detection only looks for test_*.py files, so the
        # .test.tsx file is invisible and the orchestrator trusts the LLM blindly.
        assert success is False or "no independent verification" not in msg.lower(), (
            "Orchestrator failed to detect TypeScript test file via disk-change "
            "detection — .test.tsx should be found by _extract_test_files."
        )

    def test_orchestrator_trusting_llm_message_indicates_bug(
        self, e2e_797_mock_dependencies, e2e_797_default_args, tmp_path
    ):
        """Verify the orchestrator prints the 'Trusting LLM output' message when it shouldn't.

        This test directly checks for the console output that indicates the bug:
        "No test files found for independent verification. Trusting LLM output."
        When TypeScript test files exist, this message should NOT appear.
        """
        mock_run, _, mock_console = e2e_797_mock_dependencies

        # Create TypeScript test files
        test_dir = tmp_path / "frontend" / "src" / "__test__"
        test_dir.mkdir(parents=True)
        (test_dir / "WaitlistPending.test.tsx").touch()

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step2" in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect
        e2e_797_default_args["max_cycles"] = 1
        e2e_797_default_args["issue_content"] = (
            "E2E_FILES_CREATED: frontend/src/__test__/WaitlistPending.test.tsx"
        )

        run_agentic_e2e_fix_orchestrator(**e2e_797_default_args)

        # Check console output for the "Trusting LLM" message
        all_print_calls = [
            str(call) for call in mock_console.print.call_args_list
        ]
        trusting_messages = [
            c for c in all_print_calls if "Trusting LLM output" in c
        ]

        # BUG: This message IS printed because _extract_test_files returns []
        # for TypeScript files. After fix, this message should NOT appear when
        # TypeScript test files exist.
        assert len(trusting_messages) == 0, (
            "Orchestrator printed 'Trusting LLM output' even though TypeScript "
            "test files exist. _extract_test_files failed to find .test.tsx files "
            "due to .py-only filter (issue #797).\n"
            f"Console output: {all_print_calls}"
        )
