"""
Example usage of the workflow_engine module.

Demonstrates key features: sequential execution, parallel execution,
retries, budget management, skip conditions, recovery, and dry-run mode.
"""

import sys
import os
import time

# Add the src directory to the path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "src"))

from workflow_engine import (
    WorkflowEngine,
    WorkflowConfig,
    WorkflowBuilder,
    WorkflowTemplates,
    WorkflowReportGenerator,
    WorkflowAnalyzer,
    OperationResult,
    OperationState,
    create_simple_handler,
    create_conditional_handler,
    create_recovery_handler,
)


def example_sequential_pipeline():
    """Run a simple sequential pipeline: build -> test -> deploy."""
    print("=" * 60)
    print("Example 1: Sequential Pipeline")
    print("=" * 60)

    config = WorkflowConfig(max_budget=50.0, max_retries=2)
    engine = WorkflowEngine(config)

    engine.add_operation(
        "build",
        handler=create_simple_handler(output="build artifact", cost=5.0),
        estimated_cost=5.0,
    )
    engine.add_operation(
        "test",
        handler=create_simple_handler(output="all tests pass", cost=3.0),
        dependencies=["build"],
        estimated_cost=3.0,
    )
    engine.add_operation(
        "deploy",
        handler=create_simple_handler(output="deployed to staging", cost=8.0),
        dependencies=["test"],
        estimated_cost=8.0,
    )

    result = engine.run()
    print(f"Success: {result.success}")
    print(f"Completed: {result.completed_operations}")
    print(f"Total cost: {result.total_cost:.2f}")
    print()


def example_retry_logic():
    """Demonstrate retry with a handler that fails on first 2 attempts."""
    print("=" * 60)
    print("Example 2: Retry Logic")
    print("=" * 60)

    config = WorkflowConfig(
        max_budget=100.0,
        max_retries=3,
        backoff_base=0.01,  # Fast for demo
        backoff_max=0.05,
    )
    engine = WorkflowEngine(config)

    # This handler fails on attempts 1 and 2, succeeds on attempt 3
    engine.add_operation(
        "flaky_deploy",
        handler=create_conditional_handler(
            fail_on_attempts={1, 2},
            success_cost=5.0,
            failure_cost=1.0,
        ),
        max_attempts=3,
    )

    result = engine.run()
    print(f"Success: {result.success}")
    op_result = result.operation_results.get("flaky_deploy")
    if op_result:
        print(f"Attempts used: {op_result.attempt_count}")
    print()


def example_budget_management():
    """Show budget tracking and enforcement."""
    print("=" * 60)
    print("Example 3: Budget Management")
    print("=" * 60)

    config = WorkflowConfig(max_budget=10.0, max_retries=1)
    engine = WorkflowEngine(config)

    engine.add_operation(
        "step1",
        handler=create_simple_handler(cost=4.0),
        estimated_cost=4.0,
    )
    engine.add_operation(
        "step2",
        handler=create_simple_handler(cost=4.0),
        estimated_cost=4.0,
    )
    engine.add_operation(
        "step3",
        handler=create_simple_handler(cost=4.0),
        estimated_cost=4.0,
    )

    result = engine.run()
    print(f"Success: {result.success}")
    print(f"Completed: {result.completed_operations}")
    print(f"Skipped: {result.skipped_operations}")
    print(f"Total cost: {result.total_cost:.2f} / 10.00")
    print()


def example_parallel_execution():
    """Run independent operations in parallel."""
    print("=" * 60)
    print("Example 4: Parallel Execution")
    print("=" * 60)

    config = WorkflowConfig(
        max_budget=100.0,
        parallel=True,
        max_parallel_workers=3,
    )
    engine = WorkflowEngine(config)

    engine.add_operation("setup", handler=create_simple_handler(cost=1.0))

    # These three run in parallel after setup
    for name in ["test_unit", "test_integration", "test_e2e"]:
        engine.add_operation(
            name,
            handler=create_simple_handler(cost=2.0),
            dependencies=["setup"],
        )

    engine.add_operation(
        "report",
        handler=create_simple_handler(cost=1.0),
        dependencies=["test_unit", "test_integration", "test_e2e"],
    )

    result = engine.run()
    print(f"Success: {result.success}")
    print(f"Completed: {result.completed_operations}")
    print(f"Total cost: {result.total_cost:.2f}")
    print()


def example_dry_run():
    """Preview execution plan without running."""
    print("=" * 60)
    print("Example 5: Dry Run")
    print("=" * 60)

    config = WorkflowConfig(max_budget=100.0, dry_run=True)
    engine = WorkflowEngine(config)

    engine.add_operation("build", handler=create_simple_handler(), estimated_cost=5.0)
    engine.add_operation("test", handler=create_simple_handler(), estimated_cost=3.0, dependencies=["build"])
    engine.add_operation("deploy", handler=create_simple_handler(), estimated_cost=10.0, dependencies=["test"])

    plan = engine.dry_run()
    for entry in plan:
        print(f"  {entry['operation']:15s} cost={entry['estimated_cost']:.1f}  deps={entry['dependencies']}")
    print()


def example_builder_api():
    """Use the fluent WorkflowBuilder API."""
    print("=" * 60)
    print("Example 6: Fluent Builder API")
    print("=" * 60)

    result = (
        WorkflowBuilder()
        .with_budget(50.0)
        .with_retries(2)
        .add("compile", create_simple_handler(cost=3.0))
        .add("lint", create_simple_handler(cost=1.0))
        .add("test", create_simple_handler(cost=4.0), depends_on=["compile"])
        .add("package", create_simple_handler(cost=2.0), depends_on=["compile", "lint"])
        .run()
    )

    print(f"Success: {result.success}")
    print(f"Total cost: {result.total_cost:.2f}")
    print()


def example_error_recovery():
    """Show error recovery in action."""
    print("=" * 60)
    print("Example 7: Error Recovery")
    print("=" * 60)

    def failing_handler(context):
        return OperationResult(success=False, cost=1.0, error="disk full")

    config = WorkflowConfig(max_budget=100.0, max_retries=1)
    engine = WorkflowEngine(config)

    engine.add_operation(
        "deploy",
        handler=failing_handler,
        recovery_handler=create_recovery_handler(success=True, cost=0.5),
        max_attempts=1,
    )

    result = engine.run()
    print(f"Success: {result.success}")
    print(f"Completed: {result.completed_operations}")
    print()


def example_workflow_analysis():
    """Analyze workflow structure."""
    print("=" * 60)
    print("Example 8: Workflow Analysis")
    print("=" * 60)

    config = WorkflowConfig(max_budget=100.0)
    engine = WorkflowEngine(config)

    engine.add_operation("fetch", handler=create_simple_handler(), estimated_cost=2.0)
    engine.add_operation("parse", handler=create_simple_handler(), dependencies=["fetch"], estimated_cost=3.0)
    engine.add_operation("validate", handler=create_simple_handler(), dependencies=["parse"], estimated_cost=4.0)
    engine.add_operation("transform", handler=create_simple_handler(), dependencies=["parse"], estimated_cost=5.0)
    engine.add_operation("load", handler=create_simple_handler(), dependencies=["validate", "transform"], estimated_cost=6.0)

    analyzer = WorkflowAnalyzer(engine)
    summary = analyzer.get_structure_summary()

    print(f"Total operations: {summary['total_operations']}")
    print(f"Critical path: {summary['critical_path']}")
    print(f"Parallelism factor: {summary['parallelism_factor']:.2f}")
    print(f"Bottlenecks: {summary['bottlenecks']}")
    print(f"Estimated cost: {summary['estimated_cost']:.2f}")
    print()


if __name__ == "__main__":
    example_sequential_pipeline()
    example_retry_logic()
    example_budget_management()
    example_parallel_execution()
    example_dry_run()
    example_builder_api()
    example_error_recovery()
    example_workflow_analysis()
    print("All examples completed successfully!")
