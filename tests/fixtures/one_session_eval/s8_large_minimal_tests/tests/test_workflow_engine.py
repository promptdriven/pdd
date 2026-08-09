"""Basic tests for workflow_engine module.

Only 5 tests covering ~20% of requirements. A thorough test suite should
also cover: retries, cycle detection, parallel execution, state transitions,
skip handling, dependency resolution, error recovery, and edge cases.
"""

import sys
import os
import time

# Add src directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "src"))

from workflow_engine import (
    WorkflowEngine,
    WorkflowConfig,
    Operation,
    OperationResult,
    OperationState,
)


def _success_handler(context):
    """A simple handler that always succeeds."""
    return OperationResult(success=True, cost=1.0, duration=0.01, output="ok")


def _failing_handler(context):
    """A handler that always fails."""
    return OperationResult(
        success=False, cost=0.5, duration=0.01, error="intentional failure"
    )


class TestAddAndRunSingleOperation:
    def test_add_and_run_single_operation(self):
        config = WorkflowConfig(max_budget=100.0, max_retries=1)
        engine = WorkflowEngine(config)
        engine.add_operation("build", handler=_success_handler)
        result = engine.run()
        assert result.success is True
        assert "build" in result.completed_operations


class TestOperationFailureIsReported:
    def test_operation_failure_is_reported(self):
        config = WorkflowConfig(max_budget=100.0, max_retries=1)
        engine = WorkflowEngine(config)
        engine.add_operation("deploy", handler=_failing_handler)
        result = engine.run()
        assert result.success is False
        assert "deploy" in result.failed_operations


class TestDryRunReturnsPlannedOperations:
    def test_dry_run_returns_planned_operations(self):
        config = WorkflowConfig(max_budget=100.0, dry_run=True)
        engine = WorkflowEngine(config)
        engine.add_operation("build", handler=_success_handler, estimated_cost=5.0)
        engine.add_operation("test", handler=_success_handler, estimated_cost=3.0)
        plan = engine.dry_run()
        op_names = [entry["operation"] for entry in plan]
        assert "build" in op_names
        assert "test" in op_names


class TestBudgetExceededStopsWorkflow:
    def test_budget_exceeded_stops_workflow(self):
        config = WorkflowConfig(max_budget=1.0, max_retries=1)
        engine = WorkflowEngine(config)

        def expensive_handler(context):
            return OperationResult(success=True, cost=2.0, duration=0.01, output="done")

        engine.add_operation("step1", handler=expensive_handler)
        engine.add_operation("step2", handler=expensive_handler)
        result = engine.run()
        # step2 should not have completed because budget was exceeded after step1
        assert "step2" not in result.completed_operations


class TestLogEntriesCreated:
    def test_log_entries_created(self):
        config = WorkflowConfig(max_budget=100.0, max_retries=1)
        engine = WorkflowEngine(config)
        engine.add_operation("build", handler=_success_handler)
        engine.run()
        log = engine.get_log()
        assert len(log) > 0
        event_types = [entry.event_type for entry in log]
        assert "operation_start" in event_types
