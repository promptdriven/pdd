"""E2E test for issue #572: auto-deps skipped in agentic mode allows hallucinated imports.

Exercises the REAL sync_orchestration function end-to-end in agentic mode,
verifying that hallucinated imports (non-existent local modules) are detected
after code generation when auto-deps is skipped.

Bug: In agentic mode, auto-deps is hard-coded to skip. The LLM generates code
that imports non-existent modules (e.g., firestore_writes, brevo_results_email).
No post-generation validation catches these hallucinated imports, producing
unrunnable code that passes all pipeline checks.

These tests exercise the full sync_orchestration path — from decision-making
through auto-deps skip to code generation — with only LLM calls and lock
acquisition mocked. The orchestration logic itself (auto-deps skip, crash
handling, import error detection) runs unmodified.
"""

import json
import os
import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock

import pdd
from pdd.sync_orchestration import sync_orchestration, _try_auto_fix_import_error
from pdd.sync_determine_operation import SyncDecision


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Ensure PDD_PATH is set for all tests."""
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


@pytest.fixture
def agentic_workspace(tmp_path):
    """Create a minimal workspace simulating an agentic sync project."""
    prompt = tmp_path / "prompts" / "hackathon_results_python.prompt"
    prompt.parent.mkdir(parents=True, exist_ok=True)
    prompt.write_text(
        "% Generate a hackathon results module.\n"
        "<firestore_writes>\n"
        "  <web>https://firebase.google.com/docs/firestore/manage-data/add-data</web>\n"
        "</firestore_writes>\n"
        "<brevo_results_email>\n"
        "  <web>https://developers.brevo.com/docs/send-a-transactional-email</web>\n"
        "</brevo_results_email>\n"
    )

    code_dir = tmp_path / "src"
    code_dir.mkdir(parents=True, exist_ok=True)

    example_dir = tmp_path / "examples"
    example_dir.mkdir(parents=True, exist_ok=True)

    test_dir = tmp_path / "tests"
    test_dir.mkdir(parents=True, exist_ok=True)

    meta_dir = tmp_path / ".pdd" / "meta"
    meta_dir.mkdir(parents=True, exist_ok=True)

    code = code_dir / "hackathon_results.py"
    example = example_dir / "hackathon_results_example.py"
    test = test_dir / "test_hackathon_results.py"

    return {
        'tmp_path': tmp_path,
        'prompt': prompt,
        'code': code,
        'example': example,
        'test': test,
        'meta_dir': meta_dir,
    }


def _make_decision(operation, reason='auto'):
    """Helper to create SyncDecision objects."""
    return SyncDecision(operation=operation, reason=reason)


class TestE2EIssue572AgenticHallucinatedImports:
    """E2E: sync_orchestration in agentic mode must detect hallucinated imports."""

    def _run_agentic_sync(
        self, workspace, tmp_path, monkeypatch, decisions, code_content,
        extra_patches=None, budget=10.0
    ):
        """Run sync_orchestration in agentic mode with mocked LLM operations.

        Only mocks the external boundaries (LLM calls, locks, file paths).
        The orchestration logic — including auto-deps skip, crash handling,
        and import validation — runs unmodified.
        """
        monkeypatch.chdir(tmp_path)

        call_count = [0]

        def mock_determine(*args, **kwargs):
            """Return decisions in sequence, then all_synced."""
            if call_count[0] < len(decisions):
                d = decisions[call_count[0]]
                call_count[0] += 1
                return d
            return _make_decision('all_synced', 'Complete')

        def mock_code_generator(*args, **kwargs):
            """Simulate LLM code generation by writing the provided code content."""
            workspace['code'].write_text(code_content, encoding='utf-8')
            return {'success': True, 'cost': 0.05, 'model': 'mock-model'}

        patches = {
            'pdd.sync_orchestration.get_pdd_file_paths': MagicMock(return_value={
                'prompt': workspace['prompt'],
                'code': workspace['code'],
                'example': workspace['example'],
                'test': workspace['test'],
            }),
            'pdd.sync_orchestration.sync_determine_operation': mock_determine,
            'pdd.sync_orchestration.SyncLock': MagicMock(),
            'pdd.sync_orchestration.log_event': MagicMock(),
            'pdd.sync_orchestration.append_log_entry': MagicMock(),
            'pdd.sync_orchestration._save_fingerprint_atomic': MagicMock(),
            'pdd.sync_orchestration._save_run_report_atomic': MagicMock(),
            'pdd.sync_orchestration.calculate_sha256': MagicMock(return_value='abc123'),
            'pdd.sync_orchestration.maybe_steer_operation': MagicMock(
                side_effect=lambda op, *a, **kw: (op, False)
            ),
            'pdd.sync_orchestration.create_log_entry': MagicMock(return_value={'details': {}}),
            'pdd.sync_orchestration.update_log_entry': MagicMock(),
            'pdd.sync_orchestration.load_operation_log': MagicMock(return_value=[]),
            'pdd.sync_orchestration.code_generator_main': MagicMock(
                side_effect=mock_code_generator
            ),
            # Mock other LLM operations (not the orchestration logic)
            'pdd.sync_orchestration.auto_deps_main': MagicMock(
                return_value={'success': True, 'cost': 0.01, 'model': 'mock-model'}
            ),
            'pdd.sync_orchestration.context_generator_main': MagicMock(
                return_value={'success': True, 'cost': 0.03, 'model': 'mock-model'}
            ),
            'pdd.sync_orchestration.crash_main': MagicMock(
                return_value={'success': True, 'cost': 0.08, 'model': 'mock-model'}
            ),
            'pdd.sync_orchestration.fix_verification_main': MagicMock(
                return_value={'success': True, 'cost': 0.10, 'model': 'mock-model'}
            ),
            'pdd.sync_orchestration.cmd_test_main': MagicMock(
                return_value={'success': True, 'cost': 0.06, 'model': 'mock-model'}
            ),
            'pdd.sync_orchestration.fix_main': MagicMock(
                return_value={'success': True, 'cost': 0.15, 'model': 'mock-model'}
            ),
        }

        if extra_patches:
            patches.update(extra_patches)

        ctx_managers = [patch(k, v) for k, v in patches.items()]
        for cm in ctx_managers:
            cm.start()
        try:
            return sync_orchestration(
                basename='hackathon_results',
                language='python',
                budget=budget,
                max_attempts=1,
                strength=0.5,
                temperature=0.0,
                skip_verify=True,
                skip_tests=True,
                quiet=True,
                force=True,
                no_steer=True,
                agentic_mode=True,
            )
        finally:
            for cm in ctx_managers:
                cm.stop()

    # -----------------------------------------------------------------
    # Test 1: Primary bug reproduction — hallucinated imports pass through
    # -----------------------------------------------------------------
    def test_hallucinated_imports_from_xml_tags_detected(
        self, agentic_workspace, monkeypatch
    ):
        """E2E: Hallucinated imports derived from XML tag names must be caught.

        The prompt contains <firestore_writes> and <brevo_results_email> as
        <web> documentation tags. The LLM uses these XML tag names as Python
        module imports. Since no such .py files exist, sync should fail or
        report errors.

        Currently FAILS: sync reports success=True with no errors.
        """
        hallucinated_code = (
            '"""Hackathon results module."""\n'
            'from firestore_writes import update_event_winners\n'
            'from brevo_results_email import send_bulk_notifications\n'
            '\n'
            'def calculate_results():\n'
            '    """Calculate hackathon results."""\n'
            '    winners = update_event_winners()\n'
            '    send_bulk_notifications(winners)\n'
            '    return winners\n'
        )

        result = self._run_agentic_sync(
            agentic_workspace,
            agentic_workspace['tmp_path'],
            monkeypatch,
            decisions=[
                _make_decision('auto-deps', 'Dependencies need scanning'),
            ],
            code_content=hallucinated_code,
        )

        # Verify auto-deps was skipped (it should have been converted to generate)
        assert 'generate' in result.get('operations_completed', []), (
            "auto-deps should have been skipped and advanced to generate in agentic mode"
        )

        # THE KEY ASSERTION: hallucinated imports must be detected
        # BUG: Currently result['success'] is True — hallucinated imports pass through
        has_errors = (
            result.get('success') is False
            or len(result.get('errors', [])) > 0
        )
        assert has_errors, (
            "BUG (Issue #572): Hallucinated imports (firestore_writes, "
            "brevo_results_email) passed through undetected in agentic mode. "
            f"Sync reported success={result.get('success')} with "
            f"errors={result.get('errors', [])}. Expected post-generation "
            "import validation to catch non-existent local modules."
        )

    # -----------------------------------------------------------------
    # Test 2: Wrong module name variant — close-but-wrong name
    # -----------------------------------------------------------------
    def test_wrong_module_name_variant_detected(
        self, agentic_workspace, monkeypatch
    ):
        """E2E: Import of 'hackathon_volunteer' must fail when the real module
        is 'hackathon_volunteer_management'.

        The LLM truncates the module name. Since hackathon_volunteer.py doesn't
        exist, sync should detect the invalid import.

        Currently FAILS: wrong module name passes through undetected.
        """
        # Create the REAL module with the correct (longer) name
        src_dir = agentic_workspace['code'].parent
        (src_dir / 'hackathon_volunteer_management.py').write_text(
            'def manage_volunteers():\n    """Manage volunteers."""\n    pass\n',
            encoding='utf-8'
        )

        wrong_name_code = (
            '"""Hackathon results module."""\n'
            'from hackathon_volunteer import manage_volunteers\n'
            '\n'
            'def process_results():\n'
            '    """Process hackathon results."""\n'
            '    return manage_volunteers()\n'
        )

        result = self._run_agentic_sync(
            agentic_workspace,
            agentic_workspace['tmp_path'],
            monkeypatch,
            decisions=[
                _make_decision('auto-deps', 'Dependencies need scanning'),
            ],
            code_content=wrong_name_code,
        )

        has_errors = (
            result.get('success') is False
            or len(result.get('errors', [])) > 0
        )
        assert has_errors, (
            "BUG (Issue #572): Wrong module name 'hackathon_volunteer' "
            "(actual: 'hackathon_volunteer_management') passed through undetected. "
            f"Sync reported success={result.get('success')} with "
            f"errors={result.get('errors', [])}."
        )

    # -----------------------------------------------------------------
    # Test 3: Synthetic crash message hides ModuleNotFoundError
    # -----------------------------------------------------------------
    def test_synthetic_crash_message_bypasses_import_error_detection(self):
        """E2E: _try_auto_fix_import_error fails to detect errors from synthetic messages.

        In agentic mode, the crash handler produces a synthetic delegation
        message instead of running the code. This synthetic message is passed
        to _try_auto_fix_import_error, which cannot detect the real
        ModuleNotFoundError because the regex doesn't match.

        This test exercises the actual _try_auto_fix_import_error function
        with the exact synthetic message produced in agentic mode.

        Currently FAILS: returns "No import error detected" for the synthetic message.
        """
        import tempfile

        # This is the exact synthetic message produced at sync_orchestration.py:1551
        synthetic_message = (
            "Language python (agentic_mode=True) - "
            "delegating crash detection to agentic handler.\n"
        )

        # This is the real error that WOULD occur if the code were actually run
        real_error = (
            "Traceback (most recent call last):\n"
            "  File \"hackathon_results_example.py\", line 1, in <module>\n"
            "    from hackathon_results import calculate_results\n"
            "  File \"hackathon_results.py\", line 2, in <module>\n"
            "    from firestore_writes import update_event_winners\n"
            "ModuleNotFoundError: No module named 'firestore_writes'\n"
        )

        with tempfile.NamedTemporaryFile(suffix='.py', mode='w', delete=False) as f:
            f.write('from firestore_writes import update_event_winners\n')
            code_file = Path(f.name)
        with tempfile.NamedTemporaryFile(suffix='.py', mode='w', delete=False) as f:
            f.write('from hackathon_results import calculate_results\n')
            example_file = Path(f.name)

        try:
            # The real function should detect the import error in the REAL error output
            fixed_real, msg_real = _try_auto_fix_import_error(
                real_error, code_file, example_file
            )

            # The synthetic message should also lead to error detection,
            # but currently it doesn't — that's the bug
            fixed_synthetic, msg_synthetic = _try_auto_fix_import_error(
                synthetic_message, code_file, example_file
            )

            # Verify: the real error IS detected (sanity check)
            assert "No import error detected" not in msg_real, (
                f"Real ModuleNotFoundError was not detected: {msg_real}"
            )

            # BUG: The synthetic message bypasses detection entirely
            # Expected: Either the synthetic message should not be used (code should
            # be actually run), OR import validation should happen before crash handling
            assert "No import error detected" not in msg_synthetic, (
                "BUG (Issue #572): _try_auto_fix_import_error received synthetic "
                f"delegation message and returned '{msg_synthetic}'. "
                "In agentic mode, the crash handler produces a synthetic message "
                "instead of running the code, so ModuleNotFoundError is never "
                "surfaced for detection."
            )
        finally:
            code_file.unlink(missing_ok=True)
            example_file.unlink(missing_ok=True)

    # -----------------------------------------------------------------
    # Test 4: Full pipeline — auto-deps skip + generate + crash detection
    # -----------------------------------------------------------------
    def test_full_agentic_pipeline_with_hallucinated_imports(
        self, agentic_workspace, monkeypatch
    ):
        """E2E: Full agentic pipeline should detect hallucinated imports at SOME stage.

        This exercises the complete agentic pipeline: auto-deps (skipped) →
        generate (produces hallucinated imports) → crash detection. At least
        one stage must catch the invalid imports.

        Currently FAILS: all three stages pass the hallucinated imports through.
        """
        hallucinated_code = (
            '"""Hackathon results module."""\n'
            'from firestore_writes import update_event_winners\n'
            'from brevo_results_email import send_bulk_notifications\n'
            'from hackathon_volunteer import manage_volunteers\n'
            '\n'
            'def calculate_results():\n'
            '    """Calculate hackathon results."""\n'
            '    winners = update_event_winners()\n'
            '    send_bulk_notifications(winners)\n'
            '    manage_volunteers()\n'
            '    return winners\n'
        )

        result = self._run_agentic_sync(
            agentic_workspace,
            agentic_workspace['tmp_path'],
            monkeypatch,
            decisions=[
                _make_decision('auto-deps', 'Dependencies need scanning'),
                # After generate, sync would normally check for crashes
                _make_decision('crash', 'Check generated code for crashes'),
            ],
            code_content=hallucinated_code,
        )

        # The generated code file should exist (generation succeeded)
        assert agentic_workspace['code'].exists(), "Code file should have been generated"
        code_content = agentic_workspace['code'].read_text()
        assert 'firestore_writes' in code_content, "Code should contain hallucinated import"

        # At least ONE pipeline stage should have caught the hallucinated imports
        has_errors = (
            result.get('success') is False
            or len(result.get('errors', [])) > 0
        )
        assert has_errors, (
            "BUG (Issue #572): Three hallucinated imports (firestore_writes, "
            "brevo_results_email, hackathon_volunteer) passed through the ENTIRE "
            f"agentic pipeline undetected. Result: success={result.get('success')}, "
            f"errors={result.get('errors', [])}. Neither auto-deps skip, generate, "
            "nor crash detection caught the invalid imports."
        )

    # -----------------------------------------------------------------
    # Test 5: Valid imports should NOT be flagged (no false positives)
    # -----------------------------------------------------------------
    def test_valid_imports_pass_through_agentic_mode(
        self, agentic_workspace, monkeypatch
    ):
        """E2E: Valid stdlib and local imports must not be flagged in agentic mode.

        This test ensures import validation (once implemented) doesn't cause
        false positives. Code using only stdlib and real local modules should
        pass without errors.

        Should PASS on both current and fixed code.
        """
        # Create a real local module
        src_dir = agentic_workspace['code'].parent
        (src_dir / 'utils_helper.py').write_text(
            'def helper():\n    """Helper function."""\n    return 42\n',
            encoding='utf-8'
        )

        valid_code = (
            '"""Hackathon results module."""\n'
            'import os\n'
            'import json\n'
            'from pathlib import Path\n'
            'from utils_helper import helper\n'
            '\n'
            'def calculate_results():\n'
            '    """Calculate hackathon results."""\n'
            '    return helper()\n'
        )

        result = self._run_agentic_sync(
            agentic_workspace,
            agentic_workspace['tmp_path'],
            monkeypatch,
            decisions=[
                _make_decision('auto-deps', 'Dependencies need scanning'),
            ],
            code_content=valid_code,
        )

        # Valid imports should not trigger any errors
        assert result.get('success') is True, (
            f"Valid imports should pass in agentic mode. "
            f"Got success={result.get('success')}, errors={result.get('errors', [])}"
        )

    # -----------------------------------------------------------------
    # Test 6: Sync log records the auto-deps skip event
    # -----------------------------------------------------------------
    def test_auto_deps_skip_logged_in_agentic_mode(
        self, agentic_workspace, monkeypatch
    ):
        """E2E: auto-deps skip must be logged with the correct event type.

        Verifies the sync log contains the auto_deps_skipped event with
        the expected reason message, matching the pattern from the issue report.

        Should PASS on both current and fixed code.
        """
        log_event_calls = []

        def capture_log_event(*args, **kwargs):
            """Capture log_event calls for inspection."""
            log_event_calls.append({'args': args, 'kwargs': kwargs})

        valid_code = (
            '"""Simple module."""\n'
            'import os\n'
            '\n'
            'def run():\n'
            '    """Run."""\n'
            '    return os.getcwd()\n'
        )

        # Override log_event to capture calls
        result = self._run_agentic_sync(
            agentic_workspace,
            agentic_workspace['tmp_path'],
            monkeypatch,
            decisions=[
                _make_decision('auto-deps', 'Dependencies need scanning'),
            ],
            code_content=valid_code,
            extra_patches={
                'pdd.sync_orchestration.log_event': MagicMock(side_effect=capture_log_event),
            },
        )

        # Find the auto_deps_skipped event
        skip_events = [
            call for call in log_event_calls
            if len(call['args']) >= 3 and call['args'][2] == 'auto_deps_skipped'
        ]

        assert len(skip_events) == 1, (
            f"Expected exactly 1 auto_deps_skipped log event, got {len(skip_events)}. "
            f"All events: {[c['args'][2] if len(c['args']) >= 3 else c for c in log_event_calls]}"
        )

        # Verify the reason matches the expected message from the issue report
        event_data = skip_events[0]['args'][3] if len(skip_events[0]['args']) > 3 else {}
        assert 'reason' in event_data, "auto_deps_skipped event should include a reason"
        assert 'agentic mode' in event_data['reason'].lower() or 'explicit dependencies' in event_data['reason'].lower(), (
            f"Unexpected skip reason: {event_data['reason']}"
        )
