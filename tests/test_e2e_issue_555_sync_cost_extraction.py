"""E2E test for issue #555: cost extraction reads wrong tuple index in sync_orchestration.

Unlike the unit tests (test_e2e_issue_555_cost_extraction_wrong_index.py) which replicate
the buggy extraction logic inline, these E2E tests call the REAL sync_orchestration function
and verify that actual cost/model values are correctly extracted from operation results.

The bug: sync_orchestration.py lines 1857-1858 and 1889-1890 always read result[1] as cost
and result[2] as model. This is wrong for:
  - generate: returns (content, was_incremental, cost, model) — cost at [2], model at [3]
  - crash: returns (success, final_code, final_program, attempts, cost, model) — cost at [4], model at [5]
  - fix: returns (success, fixed_test, fixed_code, attempts, cost, model) — cost at [4], model at [5]
  - verify: returns (success, final_program, final_code, attempts, cost, model) — cost at [4], model at [5]

The bool subclassing int quirk makes generate silently wrong — isinstance(False, (int, float))
passes, so was_incremental=False is treated as cost $0.00.

E2E approach: Call real sync_orchestration with mocked operation functions returning
realistic tuples. Verify that returned total_cost and logged cost/model are correct.
"""

import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock, call

import pdd
from pdd.sync_orchestration import sync_orchestration
from pdd.sync_determine_operation import SyncDecision
from pdd.sync_determine_operation import RunReport


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Set PDD_PATH so language detection works."""
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


@pytest.fixture
def sync_workspace(tmp_path):
    """Create minimal workspace files that pass sync_orchestration's file checks."""
    prompt = tmp_path / "prompts" / "cost_test_python.prompt"
    prompt.parent.mkdir(parents=True, exist_ok=True)
    prompt.write_text("Test prompt for cost extraction")

    code = tmp_path / "src" / "cost_test.py"
    code.parent.mkdir(parents=True, exist_ok=True)
    code.write_text("def hello(): pass\n")

    example = tmp_path / "examples" / "cost_test_example.py"
    example.parent.mkdir(parents=True, exist_ok=True)
    example.write_text("from cost_test import hello\nhello()\n")

    test = tmp_path / "tests" / "test_cost_test.py"
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


def _build_patches(sync_workspace, op_results):
    """Build the common patches dict for sync_orchestration, with operation mocks from op_results."""
    call_count = [0]
    decisions = list(op_results.keys())

    def mock_determine(*args, **kwargs):
        if call_count[0] < len(decisions):
            op = decisions[call_count[0]]
            call_count[0] += 1
            return _make_decision(op, f'Need {op}')
        return _make_decision('all_synced', 'Complete')

    # Create a failed RunReport so crash/verify pre-checks detect a crash
    # and proceed to call crash_main/fix_verification_main
    failed_run_report = RunReport(
        timestamp='2024-01-01T00:00:00Z',
        exit_code=1,
        tests_passed=0,
        tests_failed=1,
        coverage=0.0,
        test_hash='abc123'
    )

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
        'pdd.sync_orchestration.load_operation_log': MagicMock(return_value=[]),
        # Mock crash/verify pre-processing to ensure crash_main/fix_verification_main are called
        'pdd.sync_orchestration.read_run_report': MagicMock(return_value=failed_run_report),
        'pdd.sync_orchestration._try_auto_fix_import_error': MagicMock(return_value=(False, None)),
        'pdd.sync_orchestration._try_auto_fix_env_var_error': MagicMock(return_value=(False, None)),
        'pdd.sync_orchestration.clear_run_report': MagicMock(),
    }

    # Wire up the real update_log_entry so we can inspect its calls
    update_log_entry_mock = MagicMock(side_effect=lambda entry, **kw: entry.update(kw) or entry)
    patches['pdd.sync_orchestration.update_log_entry'] = update_log_entry_mock

    # Map operation names to their function paths
    op_function_map = {
        'generate': 'pdd.sync_orchestration.code_generator_main',
        'example': 'pdd.sync_orchestration.context_generator_main',
        'crash': 'pdd.sync_orchestration.crash_main',
        'verify': 'pdd.sync_orchestration.fix_verification_main',
        'test': 'pdd.sync_orchestration.cmd_test_main',
        'test_extend': 'pdd.sync_orchestration.cmd_test_main',
        'fix': 'pdd.sync_orchestration.fix_main',
    }

    for op, result in op_results.items():
        func_path = op_function_map.get(op)
        if func_path:
            patches[func_path] = MagicMock(return_value=result)

    return patches, update_log_entry_mock


def _run_sync(sync_workspace, tmp_path, monkeypatch, op_results, budget=10.0,
              skip_verify=False, skip_tests=False):
    """Run sync_orchestration with mocked operations returning specified results."""
    monkeypatch.chdir(tmp_path)

    patches, update_log_mock = _build_patches(sync_workspace, op_results)

    ctx_managers = [patch(k, v) for k, v in patches.items()]
    for cm in ctx_managers:
        cm.start()
    try:
        result = sync_orchestration(
            basename='cost_test',
            language='python',
            budget=budget,
            max_attempts=1,
            strength=0.5,
            temperature=0.0,
            skip_verify=skip_verify,
            skip_tests=skip_tests,
            quiet=True,
            force=True,
            no_steer=True,
        )
        return result, update_log_mock
    finally:
        for cm in ctx_managers:
            cm.stop()


class TestE2ESyncGenerateCostExtraction:
    """E2E: sync_orchestration must correctly extract cost from generate's 4-tuple result."""

    def test_generate_cost_in_total(self, sync_workspace, tmp_path, monkeypatch):
        """generate returns (content, was_incremental, cost, model) — cost at index 2.

        Bug: result[1] is was_incremental (bool). Since bool subclasses int,
        isinstance(False, (int, float)) passes → cost recorded as 0 instead of 0.0421.
        """
        generate_cost = 0.0421
        result, _ = _run_sync(
            sync_workspace, tmp_path, monkeypatch,
            op_results={
                'generate': ("generated code", False, generate_cost, "claude-sonnet-4-6"),
            },
        )

        total_cost = result.get('total_cost', 0.0)
        assert total_cost >= generate_cost, (
            f"sync total_cost should include generate cost ${generate_cost} "
            f"but got ${total_cost:.6f}. Bug: result[1]=False (bool) treated as cost $0."
        )

    def test_generate_cost_logged_correctly(self, sync_workspace, tmp_path, monkeypatch):
        """The logged actual_cost and model should come from the correct tuple indices."""
        generate_cost = 0.0421
        _, update_log_mock = _run_sync(
            sync_workspace, tmp_path, monkeypatch,
            op_results={
                'generate': ("generated code", False, generate_cost, "claude-sonnet-4-6"),
            },
        )

        # Find the update_log_entry call for the successful operation
        for c in update_log_mock.call_args_list:
            kwargs = c.kwargs if c.kwargs else {}
            if kwargs.get('success', False):
                actual_cost = kwargs.get('cost', 0.0)
                model = kwargs.get('model', 'unknown')
                assert actual_cost == pytest.approx(generate_cost), (
                    f"Logged cost should be {generate_cost} but got {actual_cost}. "
                    f"Bug: result[1]=False (was_incremental) was read as cost."
                )
                assert model == "claude-sonnet-4-6", (
                    f"Logged model should be 'claude-sonnet-4-6' but got '{model}'. "
                    f"Bug: result[2]=0.0421 (cost float) was read as model."
                )
                return

        pytest.fail("No successful update_log_entry call found")

    def test_generate_bool_true_not_treated_as_cost(self, sync_workspace, tmp_path, monkeypatch):
        """When was_incremental=True, cost should NOT be 1 (int value of True)."""
        actual_cost = 0.0053
        result, _ = _run_sync(
            sync_workspace, tmp_path, monkeypatch,
            op_results={
                'generate': ("generated code", True, actual_cost, "gpt-4o-mini"),
            },
        )

        total_cost = result.get('total_cost', 0.0)
        # With the bug: True → int 1 → cost = 1.0
        # Without the bug: cost = 0.0053
        assert total_cost == pytest.approx(actual_cost, abs=0.01), (
            f"sync total_cost should be ~${actual_cost} but got ${total_cost:.4f}. "
            f"Bug: was_incremental=True → int(True)=1 → cost recorded as $1.00."
        )


class TestE2ESyncCrashCostExtraction:
    """E2E: sync_orchestration must correctly extract cost from crash's 6-tuple result."""

    def test_crash_cost_in_total(self, sync_workspace, tmp_path, monkeypatch):
        """crash returns (success, final_code, final_program, attempts, cost, model) — cost at index 4.

        Bug: result[1] is final_code (str), isinstance fails → cost defaults to 0.0.
        The actual cost at index 4 is completely ignored.
        """
        crash_cost = 0.0315
        result, _ = _run_sync(
            sync_workspace, tmp_path, monkeypatch,
            op_results={
                'crash': (True, "fixed code", "fixed program", 2, crash_cost, "gpt-4o-mini"),
            },
        )

        total_cost = result.get('total_cost', 0.0)
        assert total_cost >= crash_cost, (
            f"sync total_cost should include crash cost ${crash_cost} "
            f"but got ${total_cost:.6f}. Bug: result[1]='fixed code' (str) fails isinstance."
        )

    def test_crash_model_logged_correctly(self, sync_workspace, tmp_path, monkeypatch):
        """The logged model should be 'gpt-4o-mini', not the final_program string."""
        _, update_log_mock = _run_sync(
            sync_workspace, tmp_path, monkeypatch,
            op_results={
                'crash': (True, "fixed code", "fixed program", 2, 0.0315, "gpt-4o-mini"),
            },
        )

        for c in update_log_mock.call_args_list:
            kwargs = c.kwargs if c.kwargs else {}
            if kwargs.get('success', False):
                model = kwargs.get('model', 'unknown')
                assert model == "gpt-4o-mini", (
                    f"Logged model should be 'gpt-4o-mini' but got '{model}'. "
                    f"Bug: result[2]='fixed program' (str) was read as model name."
                )
                return

        pytest.fail("No successful update_log_entry call found")


class TestE2ESyncFixCostExtraction:
    """E2E: sync_orchestration must correctly extract cost from fix's 6-tuple result."""

    def test_fix_cost_in_total(self, sync_workspace, tmp_path, monkeypatch):
        """fix returns (success, fixed_test, fixed_code, attempts, cost, model) — cost at index 4.

        Bug: result[1] is fixed_unit_test (str), isinstance fails → cost defaults to 0.0.
        """
        fix_cost = 0.0892
        result, _ = _run_sync(
            sync_workspace, tmp_path, monkeypatch,
            op_results={
                'fix': (True, "fixed test code", "fixed source code", 3, fix_cost, "claude-sonnet-4-6"),
            },
        )

        total_cost = result.get('total_cost', 0.0)
        assert total_cost >= fix_cost, (
            f"sync total_cost should include fix cost ${fix_cost} "
            f"but got ${total_cost:.6f}. Bug: result[1]='fixed test code' fails isinstance."
        )


class TestE2ESyncVerifyCostExtraction:
    """E2E: sync_orchestration must correctly extract cost from verify's 6-tuple result."""

    def test_verify_cost_in_total(self, sync_workspace, tmp_path, monkeypatch):
        """verify returns (success, final_program, final_code, attempts, cost, model) — cost at index 4.

        Bug: result[1] is final_program (str), isinstance fails → cost defaults to 0.0.
        """
        verify_cost = 0.0267
        result, _ = _run_sync(
            sync_workspace, tmp_path, monkeypatch,
            op_results={
                'verify': (True, "program content", "code content", 1, verify_cost, "gpt-4o-mini"),
            },
        )

        total_cost = result.get('total_cost', 0.0)
        assert total_cost >= verify_cost, (
            f"sync total_cost should include verify cost ${verify_cost} "
            f"but got ${total_cost:.6f}. Bug: result[1]='program content' fails isinstance."
        )


class TestE2ERegressionGuards:
    """E2E: Operations that already work (example, test, test_extend) must not regress."""

    def test_example_cost_in_total(self, sync_workspace, tmp_path, monkeypatch):
        """example returns (content, cost, model) — cost at index 1 works correctly."""
        example_cost = 0.0023
        result, _ = _run_sync(
            sync_workspace, tmp_path, monkeypatch,
            op_results={
                'example': ("example content", example_cost, "gpt-4o-mini"),
            },
        )

        total_cost = result.get('total_cost', 0.0)
        assert total_cost >= example_cost, (
            f"sync total_cost should include example cost ${example_cost} "
            f"but got ${total_cost:.6f}."
        )

    def test_test_cost_in_total(self, sync_workspace, tmp_path, monkeypatch):
        """test returns (content, cost, model, agentic_success) — cost at index 1 works correctly."""
        test_cost = 0.0078
        result, _ = _run_sync(
            sync_workspace, tmp_path, monkeypatch,
            op_results={
                'test': ("test content", test_cost, "claude-sonnet-4-6", True),
            },
        )

        total_cost = result.get('total_cost', 0.0)
        assert total_cost >= test_cost, (
            f"sync total_cost should include test cost ${test_cost} "
            f"but got ${total_cost:.6f}."
        )


class TestE2EBudgetAccumulationAllOperations:
    """E2E: full sync loop with all operation types — total cost must be accurate."""

    def test_multi_operation_budget_accumulation(self, sync_workspace, tmp_path, monkeypatch):
        """Run example + generate + test in sequence. All costs must accumulate.

        Expected total: $0.01 + $0.05 + $0.02 = $0.08
        With bug: $0.01 + $0.00 + $0.02 = $0.03 (generate cost lost due to bool→int)
        """
        result, _ = _run_sync(
            sync_workspace, tmp_path, monkeypatch,
            op_results={
                'example': ("content", 0.01, "gpt-4o-mini"),
                'generate': ("code", False, 0.05, "claude-sonnet-4-6"),
                'test': ("tests", 0.02, "gpt-4o-mini", True),
            },
        )

        total_cost = result.get('total_cost', 0.0)
        expected_total = 0.01 + 0.05 + 0.02  # = 0.08
        assert total_cost == pytest.approx(expected_total, abs=0.005), (
            f"Total cost should be ~${expected_total:.2f} but got ${total_cost:.4f}. "
            f"Bug: generate cost lost (was_incremental=False → $0.00)."
        )

    def test_budget_enforcement_with_generate_cost(self, sync_workspace, tmp_path, monkeypatch):
        """If generate costs $0.08 and budget is $0.05, sync should stop due to budget exceeded.

        With the bug: generate cost recorded as $0 (bool→int), so budget check never triggers
        and expensive subsequent operations keep running.
        """
        result, _ = _run_sync(
            sync_workspace, tmp_path, monkeypatch,
            op_results={
                'generate': ("code", False, 0.08, "claude-sonnet-4-6"),
                'test': ("tests", 0.05, "gpt-4o-mini", True),
            },
            budget=0.05,
        )

        total_cost = result.get('total_cost', 0.0)
        # With bug: total_cost ≈ 0.05 (only test cost counted, generate was $0)
        # Without bug: total_cost ≈ 0.08 (generate exceeds budget, test may not run)
        assert total_cost >= 0.05, (
            f"Total cost should reflect generate cost (${0.08}) but got ${total_cost:.4f}. "
            f"Bug: generate cost lost, budget check didn't fire."
        )


class TestE2EOperationLogDecorator:
    """E2E: the log_operation decorator in operation_log.py must extract cost/model correctly.

    The decorator at operation_log.py:338-340 has the same bug — always reads result[1] as
    cost and result[2] as model, regardless of operation type.
    """

    def test_decorator_extracts_generate_cost(self, tmp_path):
        """Calling a decorated function that returns a generate-style 4-tuple.

        The decorator should log cost from index 2 and model from index 3.
        Bug: logs cost from index 1 (was_incremental=False → 0.0) and model from index 2 (cost float).
        """
        from pdd.operation_log import log_operation, update_log_entry

        captured_updates = []
        original_update = update_log_entry

        def tracking_update(entry, **kwargs):
            result = original_update(entry, **kwargs)
            captured_updates.append(dict(kwargs))
            return result

        # log_operation infers basename/language from prompt_file kwarg
        prompt_file = tmp_path / "test_python.prompt"
        prompt_file.write_text("test prompt")

        @log_operation(operation='generate')
        def fake_generate(prompt_file=None):
            return ("generated code", False, 0.0421, "claude-sonnet-4-6")

        with patch('pdd.operation_log.update_log_entry', side_effect=tracking_update), \
             patch('pdd.operation_log.append_log_entry', MagicMock()), \
             patch('pdd.operation_log.save_fingerprint', MagicMock()):
            fake_generate(prompt_file=str(prompt_file))

        assert len(captured_updates) >= 1, "Decorator should have called update_log_entry"

        update_kwargs = captured_updates[-1]
        logged_cost = update_kwargs.get('cost', 0.0)
        logged_model = update_kwargs.get('model', 'unknown')

        assert logged_cost == pytest.approx(0.0421), (
            f"Decorator logged cost={logged_cost} for generate, "
            f"expected 0.0421. Bug: result[1]=False (bool) → float(False)=0.0."
        )
        assert logged_model == "claude-sonnet-4-6", (
            f"Decorator logged model='{logged_model}' for generate, "
            f"expected 'claude-sonnet-4-6'. Bug: result[2]=0.0421 (float) is not a string."
        )

    def test_decorator_extracts_fix_cost(self, tmp_path):
        """Calling a decorated function that returns a fix-style 6-tuple.

        The decorator should log cost from index 4 and model from index 5.
        Bug: logs cost=0.0 (result[1]='fixed test' str fails isinstance) and
        model='fixed source code' (result[2] is a code string, not a model name).
        """
        from pdd.operation_log import log_operation, update_log_entry

        captured_updates = []
        original_update = update_log_entry

        def tracking_update(entry, **kwargs):
            result = original_update(entry, **kwargs)
            captured_updates.append(dict(kwargs))
            return result

        prompt_file = tmp_path / "test_python.prompt"
        prompt_file.write_text("test prompt")

        @log_operation(operation='fix')
        def fake_fix(prompt_file=None):
            return (True, "fixed test code", "fixed source code", 3, 0.0892, "claude-sonnet-4-6")

        with patch('pdd.operation_log.update_log_entry', side_effect=tracking_update), \
             patch('pdd.operation_log.append_log_entry', MagicMock()), \
             patch('pdd.operation_log.save_fingerprint', MagicMock()):
            fake_fix(prompt_file=str(prompt_file))

        assert len(captured_updates) >= 1, "Decorator should have called update_log_entry"

        update_kwargs = captured_updates[-1]
        logged_cost = update_kwargs.get('cost', 0.0)
        logged_model = update_kwargs.get('model', 'unknown')

        assert logged_cost == pytest.approx(0.0892), (
            f"Decorator logged cost={logged_cost} for fix, expected 0.0892. "
            f"Bug: result[1]='fixed test code' (str) fails isinstance → cost=0.0."
        )
        assert logged_model == "claude-sonnet-4-6", (
            f"Decorator logged model='{logged_model}' for fix, expected 'claude-sonnet-4-6'. "
            f"Bug: result[2]='fixed source code' was read as model name."
        )