"""E2E test for issue #508: Budget tracker drops test/test_extend costs.

Exercises the REAL sync_orchestration function in headless mode (quiet=True),
with mocked operation functions returning 4-tuples, verifying that the actual
cost extraction logic at line 1752 correctly accumulates costs.
"""

import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock

import pdd
from pdd.sync_orchestration import sync_orchestration
from pdd.sync_determine_operation import SyncDecision


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


@pytest.fixture
def sync_workspace(tmp_path):
    """Create minimal workspace files."""
    prompt = tmp_path / "prompts" / "budget_test_python.prompt"
    prompt.parent.mkdir(parents=True, exist_ok=True)
    prompt.write_text("Test prompt")

    code = tmp_path / "src" / "budget_test.py"
    code.parent.mkdir(parents=True, exist_ok=True)
    code.write_text("def hello(): pass\n")

    example = tmp_path / "examples" / "budget_test_example.py"
    example.parent.mkdir(parents=True, exist_ok=True)
    example.write_text("from budget_test import hello\nhello()\n")

    test = tmp_path / "tests" / "test_budget_test.py"
    test.parent.mkdir(parents=True, exist_ok=True)
    test.write_text("def test_hello(): pass\n")

    return {
        'prompt': prompt,
        'code': code,
        'example': example,
        'test': test,
    }


def _make_decision(operation, reason='auto'):
    return SyncDecision(operation=operation, reason=reason)


class TestE2ESyncBudgetTracking:
    """E2E: sync_orchestration must accumulate costs from 4-tuple test results."""

    def _run_sync(self, sync_workspace, tmp_path, monkeypatch, decisions, op_results, budget=10.0):
        """Run sync_orchestration with mocked operations returning specified results."""
        monkeypatch.chdir(tmp_path)

        call_count = [0]
        def mock_determine(*args, **kwargs):
            if call_count[0] < len(decisions):
                d = decisions[call_count[0]]
                call_count[0] += 1
                return d
            return _make_decision('all_synced', 'Complete')

        patches = {
            'pdd.sync_orchestration.get_pdd_file_paths': MagicMock(return_value=sync_workspace),
            'pdd.sync_orchestration.sync_determine_operation': mock_determine,
            'pdd.sync_orchestration.SyncLock': MagicMock(),
            'pdd.sync_orchestration.log_event': MagicMock(),
            'pdd.sync_orchestration.append_log_entry': MagicMock(),
            'pdd.sync_orchestration._save_fingerprint_atomic': MagicMock(),
            'pdd.sync_orchestration._save_run_report_atomic': MagicMock(),
            'pdd.sync_orchestration.calculate_sha256': MagicMock(return_value='abc123'),
            'pdd.sync_orchestration.maybe_steer_operation': MagicMock(side_effect=lambda op, *a, **kw: (op, False)),
            'pdd.sync_orchestration.create_log_entry': MagicMock(return_value={'details': {}}),
            'pdd.sync_orchestration.update_log_entry': MagicMock(),
            'pdd.sync_orchestration.load_operation_log': MagicMock(return_value=[]),
        }

        if 'test' in op_results or 'test_extend' in op_results:
            test_result = op_results.get('test') or op_results.get('test_extend')
            patches['pdd.sync_orchestration.cmd_test_main'] = MagicMock(return_value=test_result)
        if 'generate' in op_results:
            patches['pdd.sync_orchestration.code_generator_main'] = MagicMock(return_value=op_results['generate'])

        ctx_managers = [patch(k, v) for k, v in patches.items()]
        for cm in ctx_managers:
            cm.start()
        try:
            return sync_orchestration(
                basename='budget_test',
                language='python',
                budget=budget,
                max_attempts=1,
                strength=0.5,
                temperature=0.0,
                skip_verify=True,
                skip_tests=False,
                quiet=True,
                force=True,
                no_steer=True,
            )
        finally:
            for cm in ctx_managers:
                cm.stop()

    def test_sync_tracks_test_4tuple_cost(self, sync_workspace, tmp_path, monkeypatch):
        """Bug: 4-tuple test result cost is dropped because result[-2] gives model name."""
        test_cost = 0.0007821
        result = self._run_sync(
            sync_workspace, tmp_path, monkeypatch,
            decisions=[_make_decision('test', 'Need tests')],
            op_results={'test': ("test content", test_cost, "gpt-4o-mini", True)},
        )

        total_cost = result.get('total_cost', 0.0)
        assert total_cost >= test_cost, (
            f"sync total_cost should include test cost ${test_cost} "
            f"but got ${total_cost:.6f}. Bug: result[-2] on 4-tuple gives model name, not cost."
        )

    def test_sync_budget_enforcement_with_test_cost(self, sync_workspace, tmp_path, monkeypatch):
        """generate($0.05) + test($0.10) = $0.15 should exceed budget $0.12."""
        result = self._run_sync(
            sync_workspace, tmp_path, monkeypatch,
            decisions=[
                _make_decision('generate', 'Need code'),
                _make_decision('test', 'Need tests'),
                _make_decision('test_extend', 'More coverage'),
            ],
            op_results={
                'generate': ("code", 0.05, "gpt-4o-mini"),
                'test': ("tests", 0.10, "gpt-4o-mini", True),
            },
            budget=0.12,
        )

        total_cost = result.get('total_cost', 0.0)
        assert total_cost >= 0.12, (
            f"Total should be >= $0.12 (gen $0.05 + test $0.10) but got ${total_cost:.4f}. "
            f"Bug drops test cost so budget check never fires."
        )
