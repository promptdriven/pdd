"""
E2E Tests for Issue #620: pdd generate hallucinates Python module exports that don't exist.

These tests exercise the full sync_orchestration() → code_generator_main() →
_validate_python_imports() code path with real filesystem modules. Only LLM calls
and TUI/locking infrastructure are mocked. The buggy _validate_python_imports()
function is NOT mocked — it runs against real files with real AST parsing.

Bug: _validate_python_imports() in pdd/sync_orchestration.py only checks whether
local module *files* exist on disk. It does NOT verify that the specific imported
*names* (functions, classes, constants) actually exist within those modules. This
allows hallucinated imports like:
  - from hackathon_models import get_event  (module has only TypedDicts)
  - from utils.firebase_admin_init import db  (submodule doesn't exist)
  - from hackathon_auth import require_auth  (actual name is require_hackathon_role)

User-facing impact: `pdd sync` in agentic mode silently accepts generated code
with broken imports, leading to runtime ImportErrors in downstream code.
"""

import os
import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest

from pdd.sync_orchestration import sync_orchestration
from pdd.sync_determine_operation import SyncDecision


# ---------------------------------------------------------------------------
# Fixture: Minimal orchestration environment with REAL _validate_python_imports
# ---------------------------------------------------------------------------

@pytest.fixture
def e2e_sync_fixture(tmp_path):
    """Set up a minimal sync environment that exercises the real validation path.

    Mocks only external dependencies (LLM, TUI, locking, logging) but leaves
    _validate_python_imports() unmocked so it runs against real files on disk.
    """
    # Create project structure
    (tmp_path / "prompts").mkdir()
    (tmp_path / "src").mkdir()
    (tmp_path / "examples").mkdir()
    (tmp_path / "tests").mkdir()
    pdd_meta_dir = tmp_path / ".pdd" / "meta"
    pdd_meta_dir.mkdir(parents=True)

    # Create a dummy prompt file
    (tmp_path / "prompts" / "calculator_python.prompt").write_text(
        "Create a calculator module."
    )

    monkeypatch = pytest.MonkeyPatch()
    monkeypatch.chdir(tmp_path)

    # Mock SyncApp to run worker synchronously (no TUI)
    def mock_sync_app_run(self):
        """Execute worker synchronously instead of via TUI."""
        try:
            return self.worker_func()
        except Exception as e:
            return {
                "success": False,
                "total_cost": 0.0,
                "model_name": "",
                "error": str(e),
                "operations_completed": [],
                "errors": [f"{type(e).__name__}: {e}"],
            }

    # Clear CI env var to prevent headless mode issues
    env_without_ci = {k: v for k, v in os.environ.items() if k != "CI"}

    with (
        patch.dict(os.environ, env_without_ci, clear=True),
        patch("pdd.sync_orchestration.sync_determine_operation") as mock_determine,
        patch("pdd.sync_orchestration.SyncLock") as mock_lock,
        patch("pdd.sync_orchestration.SyncApp") as mock_sync_app_class,
        patch("pdd.sync_orchestration.code_generator_main") as mock_code_gen,
        patch("pdd.sync_orchestration.auto_deps_main") as mock_auto_deps,
        patch("pdd.sync_orchestration.context_generator_main") as mock_context_gen,
        patch("pdd.sync_orchestration.crash_main") as mock_crash,
        patch("pdd.sync_orchestration.fix_verification_main") as mock_verify,
        patch("pdd.sync_orchestration.cmd_test_main") as mock_test,
        patch("pdd.sync_orchestration.fix_main") as mock_fix,
        patch("pdd.sync_orchestration.update_main") as mock_update,
        patch("pdd.sync_orchestration.save_run_report") as mock_save_report,
        patch("pdd.sync_orchestration._display_sync_log") as mock_display_log,
        patch("pdd.sync_orchestration._save_fingerprint_atomic") as mock_save_fp,
        patch("pdd.sync_orchestration.get_pdd_file_paths") as mock_get_paths,
        patch.object(sys.stdout, "isatty", return_value=True),
    ):
        # Configure SyncApp mock
        def store_worker_func(*args, **kwargs):
            instance = MagicMock()
            instance.worker_func = kwargs.get("worker_func", lambda: {"success": True})
            instance.run = lambda: mock_sync_app_run(instance)
            return instance

        mock_sync_app_class.side_effect = store_worker_func

        # Configure lock mock
        mock_lock.return_value.__enter__.return_value = mock_lock
        mock_lock.return_value.__exit__.return_value = None

        # Configure path mocks
        mock_get_paths.return_value = {
            "prompt": tmp_path / "prompts" / "calculator_python.prompt",
            "code": tmp_path / "src" / "calculator.py",
            "example": tmp_path / "examples" / "calculator_example.py",
            "test": tmp_path / "tests" / "test_calculator.py",
        }

        # Default return values for operations we don't exercise
        mock_auto_deps.return_value = {"success": True, "cost": 0.01, "model": "mock"}
        mock_context_gen.return_value = {"success": True, "cost": 0.03, "model": "mock"}
        mock_crash.return_value = {"success": True, "cost": 0.08, "model": "mock"}
        mock_verify.return_value = {"success": True, "cost": 0.10, "model": "mock"}
        mock_test.return_value = {"success": True, "cost": 0.06, "model": "mock"}
        mock_fix.return_value = {"success": True, "cost": 0.15, "model": "mock"}
        mock_update.return_value = {"success": True, "cost": 0.04, "model": "mock"}
        mock_display_log.return_value = {"success": True, "log_entries": []}

        yield {
            "tmp_path": tmp_path,
            "sync_determine_operation": mock_determine,
            "code_generator_main": mock_code_gen,
            "get_pdd_file_paths": mock_get_paths,
        }

    monkeypatch.undo()


# ---------------------------------------------------------------------------
# Test 1: Hallucinated functions from a TypedDict-only module
# ---------------------------------------------------------------------------


class TestIssue620E2E:
    """E2E tests exercising the full sync_orchestration → _validate_python_imports path."""

    def test_hallucinated_functions_from_typeddict_module(self, e2e_sync_fixture):
        """
        Issue #620 Scenario 1: sync_orchestration() should detect hallucinated
        function names imported from a module that only contains TypedDicts.

        Setup: hackathon_models.py exists with TypedDicts only, generated code
        imports get_event, create_submission, list_submissions from it.

        Bug: _validate_python_imports() sees hackathon_models.py exists and
        immediately skips to the next module — never checking if the imported
        names actually exist. sync_orchestration() reports success.

        Expected (after fix): sync_orchestration() reports an error about
        hallucinated imports.
        """
        tmp_path = e2e_sync_fixture["tmp_path"]
        mock_determine = e2e_sync_fixture["sync_determine_operation"]
        mock_code_gen = e2e_sync_fixture["code_generator_main"]

        # Create a REAL local module with only TypedDicts — no functions
        (tmp_path / "src" / "hackathon_models.py").write_text(
            '"""Hackathon data models."""\n'
            "from typing import TypedDict\n"
            "\n"
            "class Submission(TypedDict):\n"
            "    id: str\n"
            "    title: str\n"
            "    description: str\n"
            "\n"
            "class Event(TypedDict):\n"
            "    id: str\n"
            "    name: str\n",
            encoding="utf-8",
        )

        # Generated code with hallucinated function imports
        hallucinated_code = (
            '"""Hackathon submission handler."""\n'
            "from hackathon_models import get_event, create_submission, list_submissions\n"
            "\n"
            "def handle_submission():\n"
            '    """Handle a hackathon submission."""\n'
            "    event = get_event()\n"
            "    return create_submission(event)\n"
        )

        def mock_generate(*args, **kwargs):
            """Mock code_generator_main that writes code with hallucinated imports."""
            code_file = tmp_path / "src" / "calculator.py"
            code_file.write_text(hallucinated_code, encoding="utf-8")
            return {"success": True, "cost": 0.05, "model": "mock-model"}

        mock_code_gen.side_effect = mock_generate

        # Trigger generate → all_synced (the validation runs after generate)
        mock_determine.side_effect = [
            SyncDecision(operation="generate", reason="New module needs generation"),
            SyncDecision(operation="all_synced", reason="All done"),
        ]

        result = sync_orchestration(
            basename="calculator", language="python", agentic_mode=True
        )

        # Bug #620: Currently passes because _validate_python_imports() only checks
        # that hackathon_models.py exists on disk — never verifying that get_event,
        # create_submission, or list_submissions are defined in it.
        has_errors = len(result.get("errors", [])) > 0
        assert has_errors, (
            "Bug #620 E2E: hackathon_models.py contains only TypedDicts (Submission, Event), "
            "but generated code imports get_event, create_submission, list_submissions. "
            "sync_orchestration() should have detected these hallucinated imports but "
            f"reported: success={result.get('success')}, errors={result.get('errors', [])}"
        )

    def test_nonexistent_submodule_path(self, e2e_sync_fixture):
        """
        Issue #620 Scenario 2: sync_orchestration() should detect imports from
        non-existent submodule paths.

        Setup: utils/ package exists but utils/firebase_admin_init.py does not.
        Generated code has 'from utils.firebase_admin_init import db'.

        Bug: _validate_python_imports() extracts only the top-level module name
        ('utils') via node.module.split('.')[0], sees utils/__init__.py exists,
        and skips validation. The full submodule path is never checked.

        Expected (after fix): sync_orchestration() reports an error about the
        non-existent submodule.
        """
        tmp_path = e2e_sync_fixture["tmp_path"]
        mock_determine = e2e_sync_fixture["sync_determine_operation"]
        mock_code_gen = e2e_sync_fixture["code_generator_main"]

        # Create a utils package WITHOUT firebase_admin_init submodule
        utils_dir = tmp_path / "src" / "utils"
        utils_dir.mkdir(parents=True)
        (utils_dir / "__init__.py").write_text('"""Utils package."""\n', encoding="utf-8")
        (utils_dir / "helpers.py").write_text(
            '"""Utility helpers."""\n'
            "def format_date(d): return str(d)\n",
            encoding="utf-8",
        )

        # Generated code importing from non-existent submodule
        bad_import_code = (
            '"""Hackathon results module."""\n'
            "from utils.firebase_admin_init import db\n"
            "\n"
            "def get_results():\n"
            '    """Get hackathon results."""\n'
            '    return db.collection("results").get()\n'
        )

        def mock_generate(*args, **kwargs):
            """Mock code_generator_main that writes code importing non-existent submodule."""
            code_file = tmp_path / "src" / "calculator.py"
            code_file.write_text(bad_import_code, encoding="utf-8")
            return {"success": True, "cost": 0.05, "model": "mock-model"}

        mock_code_gen.side_effect = mock_generate

        mock_determine.side_effect = [
            SyncDecision(operation="generate", reason="New module needs generation"),
            SyncDecision(operation="all_synced", reason="All done"),
        ]

        result = sync_orchestration(
            basename="calculator", language="python", agentic_mode=True
        )

        # Bug #620: _validate_python_imports() extracts 'utils' (top-level only),
        # finds utils/__init__.py, and skips. The full path utils.firebase_admin_init
        # is never checked.
        has_errors = len(result.get("errors", [])) > 0
        assert has_errors, (
            "Bug #620 E2E: utils/ package exists but utils/firebase_admin_init.py does not. "
            "Generated code imports 'from utils.firebase_admin_init import db'. "
            "sync_orchestration() should have detected the non-existent submodule but "
            f"reported: success={result.get('success')}, errors={result.get('errors', [])}"
        )

    def test_wrong_function_name_from_auth_module(self, e2e_sync_fixture):
        """
        Issue #620 Scenario 3: sync_orchestration() should detect when generated
        code imports a function name that doesn't match the actual export.

        Setup: hackathon_auth.py exports require_hackathon_role, but generated
        code imports require_auth.

        Bug: _validate_python_imports() sees hackathon_auth.py exists on disk and
        immediately continues — never inspecting whether 'require_auth' is defined.

        Expected (after fix): sync_orchestration() reports an error about the
        wrong function name.
        """
        tmp_path = e2e_sync_fixture["tmp_path"]
        mock_determine = e2e_sync_fixture["sync_determine_operation"]
        mock_code_gen = e2e_sync_fixture["code_generator_main"]

        # Create auth module with the CORRECT function name
        (tmp_path / "src" / "hackathon_auth.py").write_text(
            '"""Hackathon authentication module."""\n'
            "\n"
            "def require_hackathon_role(role: str):\n"
            '    """Require the caller to have a specific hackathon role."""\n'
            "    pass\n",
            encoding="utf-8",
        )

        # Generated code imports the WRONG function name
        wrong_name_code = (
            '"""Hackathon judging module."""\n'
            "from hackathon_auth import require_auth\n"
            "\n"
            "def judge_submission(submission_id: str):\n"
            '    """Judge a hackathon submission."""\n'
            '    require_auth("judge")\n'
            '    return {"judged": True}\n'
        )

        def mock_generate(*args, **kwargs):
            """Mock code_generator_main that writes code with wrong function name."""
            code_file = tmp_path / "src" / "calculator.py"
            code_file.write_text(wrong_name_code, encoding="utf-8")
            return {"success": True, "cost": 0.05, "model": "mock-model"}

        mock_code_gen.side_effect = mock_generate

        mock_determine.side_effect = [
            SyncDecision(operation="generate", reason="New module needs generation"),
            SyncDecision(operation="all_synced", reason="All done"),
        ]

        result = sync_orchestration(
            basename="calculator", language="python", agentic_mode=True
        )

        # Bug #620: hackathon_auth.py exists → validation skips it entirely.
        # require_auth is never checked against the actual exports.
        has_errors = len(result.get("errors", [])) > 0
        assert has_errors, (
            "Bug #620 E2E: hackathon_auth.py exports 'require_hackathon_role', "
            "but generated code imports 'require_auth'. "
            "sync_orchestration() should have detected this wrong function name but "
            f"reported: success={result.get('success')}, errors={result.get('errors', [])}"
        )

    def test_valid_imports_not_flagged(self, e2e_sync_fixture):
        """
        Regression guard: Valid imports from a real module should NOT be flagged.

        This ensures the fix doesn't introduce false positives when imported names
        actually exist in the target module.
        """
        tmp_path = e2e_sync_fixture["tmp_path"]
        mock_determine = e2e_sync_fixture["sync_determine_operation"]
        mock_code_gen = e2e_sync_fixture["code_generator_main"]

        # Create a module with real, importable functions
        (tmp_path / "src" / "hackathon_helpers.py").write_text(
            '"""Hackathon helper utilities."""\n'
            "\n"
            "def format_score(score: float) -> str:\n"
            '    """Format a score for display."""\n'
            '    return f"{score:.2f}"\n'
            "\n"
            "def validate_submission(data: dict) -> bool:\n"
            '    """Validate submission data."""\n'
            '    return "title" in data\n',
            encoding="utf-8",
        )

        # Generated code with VALID imports
        valid_code = (
            '"""Hackathon display module."""\n'
            "from hackathon_helpers import format_score, validate_submission\n"
            "\n"
            "def display_results(submissions):\n"
            '    """Display hackathon results."""\n'
            "    for s in submissions:\n"
            "        if validate_submission(s):\n"
            '            print(format_score(s["score"]))\n'
        )

        def mock_generate(*args, **kwargs):
            """Mock code_generator_main that writes code with valid imports."""
            code_file = tmp_path / "src" / "calculator.py"
            code_file.write_text(valid_code, encoding="utf-8")
            return {"success": True, "cost": 0.05, "model": "mock-model"}

        mock_code_gen.side_effect = mock_generate

        mock_determine.side_effect = [
            SyncDecision(operation="generate", reason="New module needs generation"),
            SyncDecision(operation="all_synced", reason="All done"),
        ]

        result = sync_orchestration(
            basename="calculator", language="python", agentic_mode=True
        )

        # Valid imports should never trigger errors
        import_errors = [
            e for e in result.get("errors", []) if "import" in e.lower()
        ]
        assert len(import_errors) == 0, (
            "Regression: Valid imports (format_score, validate_submission) from "
            "hackathon_helpers.py should NOT be flagged as hallucinated. "
            f"Got import-related errors: {import_errors}"
        )
