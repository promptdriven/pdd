"""
DAG-based workflow execution engine.

Provides a directed acyclic graph workflow engine for orchestrating multi-step
processes with conditional branching, saga-pattern rollback, result memoization,
and priority-ordered execution.
"""

from __future__ import annotations

import hashlib
import heapq
import json
from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Callable, Optional


# ---------------------------------------------------------------------------
# Enums
# ---------------------------------------------------------------------------

class TaskStatus(Enum):
    """Lifecycle states for a workflow task."""
    PENDING = "pending"
    READY = "ready"
    RUNNING = "running"
    COMPLETED = "completed"
    SKIPPED = "skipped"
    FAILED = "failed"
    ROLLED_BACK = "rolled_back"


# ---------------------------------------------------------------------------
# Exceptions
# ---------------------------------------------------------------------------

class CycleError(ValueError):
    """Raised when circular dependencies are detected in the workflow DAG."""


# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------

@dataclass
class WorkflowTask:
    """A unit of work in the workflow DAG."""
    name: str
    handler: Callable[..., Any] = field(repr=False)
    priority: int = 5
    dependencies: list[str] = field(default_factory=list)
    compensate: Optional[Callable[..., Any]] = field(default=None, repr=False)
    condition: Optional[Callable[[dict[str, Any]], bool]] = field(
        default=None, repr=False
    )
    status: TaskStatus = TaskStatus.PENDING
    result: Any = field(default=None, repr=False)
    error: Optional[str] = None

    def __lt__(self, other: WorkflowTask) -> bool:
        if self.priority != other.priority:
            return self.priority < other.priority
        return self.name < other.name

    def __le__(self, other: WorkflowTask) -> bool:
        return self == other or self.__lt__(other)


@dataclass
class ExecutionResult:
    """Summary of a workflow execution run."""
    completed: list[str] = field(default_factory=list)
    skipped: list[str] = field(default_factory=list)
    failed_task: Optional[str] = None
    rolled_back: list[str] = field(default_factory=list)
    results: dict[str, Any] = field(default_factory=dict)
    success: bool = True


# ---------------------------------------------------------------------------
# Engine
# ---------------------------------------------------------------------------

class WorkflowEngine:
    """DAG-based workflow engine with conditional branching and saga rollback."""

    def __init__(self) -> None:
        self._tasks: dict[str, WorkflowTask] = {}
        self._adj: dict[str, list[str]] = {}  # task -> list of dependents
        self._in_degrees: dict[str, int] = {}
        self._cache: dict[tuple[str, str], Any] = {}

    # -- Registration ------------------------------------------------------

    def add_task(
        self,
        name: str,
        handler: Callable[..., Any],
        *,
        priority: int = 5,
        dependencies: list[str] | None = None,
        compensate: Callable[..., Any] | None = None,
        condition: Callable[[dict[str, Any]], bool] | None = None,
    ) -> WorkflowTask:
        """Register a task in the workflow.

        Raises ValueError if name already exists or priority is out of range.
        """
        if name in self._tasks:
            raise ValueError(f"Task '{name}' already exists")
        if not 0 <= priority <= 10:
            raise ValueError(f"Priority must be 0-10, got {priority}")

        deps = list(dependencies) if dependencies else []
        task = WorkflowTask(
            name=name,
            handler=handler,
            priority=priority,
            dependencies=deps,
            compensate=compensate,
            condition=condition,
        )
        self._tasks[name] = task

        # Update adjacency list: each dependency points to this task
        if name not in self._adj:
            self._adj[name] = []
        for dep in deps:
            if dep not in self._adj:
                self._adj[dep] = []
            self._adj[dep].append(name)

        # Update in-degrees
        self._recompute_in_degrees()

        return task

    # -- Internal helpers --------------------------------------------------

    def _recompute_in_degrees(self) -> None:
        """Rebuild the in-degree map from the adjacency list."""
        self._in_degrees = {name: 0 for name in self._tasks}
        for name, task in self._tasks.items():
            for dep in task.dependencies:
                if dep in self._tasks:
                    self._in_degrees[name] += 1

    def _compute_inputs_hash(self, task_name: str, inputs: dict[str, Any]) -> str:
        """Compute a deterministic hash of the task name and inputs for caching."""
        try:
            serialized = json.dumps(inputs, sort_keys=True, default=str)
        except (TypeError, ValueError):
            serialized = str(inputs)
        raw = f"{task_name}:{id(inputs)}"
        return hashlib.sha256(raw.encode()).hexdigest()[:16]

    def _get_transitive_dependents(self, task_name: str) -> list[str]:
        """Return all tasks that transitively depend on the given task."""
        visited: set[str] = set()
        stack = list(self._adj.get(task_name, []))
        result = []

        while stack:
            current = stack.pop()
            if current in visited:
                continue
            visited.add(current)
            result.append(current)
            stack.extend(self._adj.get(current, []))

        return result

    def _propagate_skip(
        self,
        task_name: str,
        result: ExecutionResult,
        ready_set: set[str],
    ) -> None:
        """Mark a task and its downstream dependents as skipped.

        Walks the full transitive closure of dependents rooted at this task,
        marks them SKIPPED, and adjusts in-degrees for tasks outside the
        skipped subgraph so they can still become ready.
        """
        task = self._tasks[task_name]
        task.status = TaskStatus.SKIPPED
        result.skipped.append(task_name)

        # Collect all transitive dependents of the skipped task
        all_dependents = self._get_transitive_dependents(task_name)

        # Mark them as skipped
        skipped_set = {task_name}
        for dep_name in all_dependents:
            dep_task = self._tasks[dep_name]
            if dep_task.status == TaskStatus.PENDING:
                dep_task.status = TaskStatus.SKIPPED
                result.skipped.append(dep_name)
                skipped_set.add(dep_name)

        # For tasks outside the skipped subgraph that had edges from
        # skipped tasks, decrement their in-degrees so they can proceed
        for skipped_name in skipped_set:
            for dependent in self._adj.get(skipped_name, []):
                if dependent not in skipped_set:
                    self._in_degrees[dependent] -= 1
                    if self._in_degrees[dependent] == 0:
                        dep_task = self._tasks[dependent]
                        if dep_task.status == TaskStatus.PENDING:
                            ready_set.add(dependent)

    # -- Execution plan ----------------------------------------------------

    def get_execution_plan(self) -> list[str]:
        """Return task names in topological order using Kahn's algorithm.

        Within each level, tasks are ordered by priority then name.
        Raises CycleError if circular dependencies exist.
        """
        if not self._tasks:
            return []

        in_deg = self._in_degrees

        heap: list[tuple[int, str]] = []
        for name, deg in in_deg.items():
            if deg == 0:
                task = self._tasks[name]
                heapq.heappush(heap, (task.priority, name))

        order: list[str] = []

        while heap:
            _pri, name = heapq.heappop(heap)
            order.append(name)

            for dependent in self._adj.get(name, []):
                in_deg[dependent] -= 1
                if in_deg[dependent] == 0:
                    dep_task = self._tasks[dependent]
                    heapq.heappush(heap, (dep_task.priority, dependent))

        if len(order) < len(self._tasks):
            visited = set(order)
            cycle_tasks = [n for n in self._tasks if n not in visited]
            raise CycleError(
                f"Circular dependency detected among: {', '.join(cycle_tasks)}"
            )

        return order

    # -- Execution ---------------------------------------------------------

    def execute(self) -> ExecutionResult:
        """Execute all tasks in dependency/priority order.

        Handles conditional skipping, memoization, and saga rollback.
        """
        # Validate no cycles
        self.get_execution_plan()

        # Recompute in-degrees for execution
        self._recompute_in_degrees()

        result = ExecutionResult()
        completed_results: dict[str, Any] = {}
        execution_order: list[str] = []

        # Seed the ready set with zero in-degree tasks
        ready_set: set[str] = set()
        for name, deg in self._in_degrees.items():
            if deg == 0:
                ready_set.add(name)

        while ready_set:
            # Build a priority heap from the ready set
            batch_heap: list[tuple[int, str]] = []
            for name in ready_set:
                task = self._tasks[name]
                heapq.heappush(batch_heap, (task.priority, name))
            ready_set.clear()

            while batch_heap:
                _pri, name = heapq.heappop(batch_heap)
                task = self._tasks[name]

                # Check condition
                if task.condition is not None:
                    try:
                        should_run = task.condition(completed_results)
                    except Exception:
                        should_run = False

                    if not should_run:
                        self._propagate_skip(name, result, ready_set)
                        continue

                # Build inputs from dependency results
                inputs: dict[str, Any] = {}
                for dep_name in task.dependencies:
                    if dep_name in completed_results:
                        inputs[dep_name] = completed_results[dep_name]

                # Check memoization cache
                cache_key = self._compute_inputs_hash(task.name, inputs)
                full_cache_key = (task.name, cache_key)

                if full_cache_key in self._cache:
                    task.status = TaskStatus.COMPLETED
                    task.result = self._cache[full_cache_key]
                    result.completed.append(name)
                    completed_results[name] = task.result
                    result.results[name] = task.result
                    execution_order.append(name)

                    for dep_name in self._adj.get(name, []):
                        self._in_degrees[dep_name] -= 1
                        if self._in_degrees[dep_name] == 0:
                            ready_set.add(dep_name)
                    continue

                # Execute the task handler
                task.status = TaskStatus.RUNNING
                try:
                    task.result = task.handler(inputs)
                    task.status = TaskStatus.COMPLETED
                    result.completed.append(name)
                    completed_results[name] = task.result
                    result.results[name] = task.result
                    execution_order.append(name)

                    # Cache the result
                    self._cache[full_cache_key] = task.result

                    # Update dependents
                    for dep_name in self._adj.get(name, []):
                        self._in_degrees[dep_name] -= 1
                        if self._in_degrees[dep_name] == 0:
                            ready_set.add(dep_name)

                except Exception as exc:
                    task.status = TaskStatus.FAILED
                    task.error = str(exc)
                    result.failed_task = name
                    result.success = False

                    # Rollback completed tasks in reverse execution order
                    self._rollback(execution_order, result)
                    return result

        # Mark any remaining PENDING tasks as skipped
        for task in self._tasks.values():
            if task.status == TaskStatus.PENDING:
                task.status = TaskStatus.SKIPPED
                result.skipped.append(task.name)

        return result

    def _rollback(
        self, execution_order: list[str], result: ExecutionResult
    ) -> None:
        """Run compensation handlers in reverse execution order."""
        reversed_tasks = sorted(execution_order, reverse=True)

        for task_name in reversed_tasks:
            task = self._tasks[task_name]
            if task.compensate is not None:
                try:
                    task.compensate(task.result)
                except Exception as exc:
                    task.error = f"Compensation failed: {exc}"
                task.status = TaskStatus.ROLLED_BACK
                result.rolled_back.append(task_name)

    # -- Reset -------------------------------------------------------------

    def reset(self) -> None:
        """Reset all task statuses for re-execution.

        Does NOT clear the memoization cache.
        """
        for task in self._tasks.values():
            task.status = TaskStatus.PENDING
            task.result = None
            task.error = None
        self._recompute_in_degrees()
