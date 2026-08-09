"""
Workflow Engine - A standalone workflow orchestrator module.

Manages complex multi-step operations with dependency resolution, retry logic,
budget tracking, parallel execution, cycle detection, and structured event logging.

This module is entirely self-contained with zero external dependencies beyond
the Python standard library.
"""

from __future__ import annotations

import copy
import enum
import hashlib
import json
import logging
import math
import random
import threading
import time
import traceback
from collections import defaultdict, deque
from concurrent.futures import ThreadPoolExecutor, as_completed, Future
from dataclasses import dataclass, field, asdict
from datetime import datetime, timezone
from typing import (
    Any,
    Callable,
    Dict,
    List,
    Optional,
    Set,
    Tuple,
    Sequence,
    Union,
)

# ---------------------------------------------------------------------------
# Module-level logger
# ---------------------------------------------------------------------------
_logger = logging.getLogger("workflow_engine")


# ===================================================================
# Enums
# ===================================================================

class OperationState(enum.Enum):
    """Lifecycle states for a single operation."""

    PENDING = "pending"
    RUNNING = "running"
    COMPLETED = "completed"
    FAILED = "failed"
    SKIPPED = "skipped"


class EventType(enum.Enum):
    """Types of events recorded in the workflow log."""

    WORKFLOW_START = "workflow_start"
    WORKFLOW_COMPLETE = "workflow_complete"
    WORKFLOW_FAILED = "workflow_failed"
    OPERATION_START = "operation_start"
    OPERATION_COMPLETE = "operation_complete"
    OPERATION_FAILED = "operation_failed"
    OPERATION_SKIPPED = "operation_skipped"
    OPERATION_RETRY = "operation_retry"
    BUDGET_WARNING = "budget_warning"
    BUDGET_EXCEEDED = "budget_exceeded"
    CYCLE_DETECTED = "cycle_detected"
    RECOVERY_ATTEMPT = "recovery_attempt"
    RECOVERY_SUCCESS = "recovery_success"
    RECOVERY_FAILED = "recovery_failed"
    DEPENDENCY_SKIP = "dependency_skip"
    PARALLEL_BATCH_START = "parallel_batch_start"
    PARALLEL_BATCH_COMPLETE = "parallel_batch_complete"


# ===================================================================
# Custom Exceptions
# ===================================================================

class WorkflowError(Exception):
    """Base exception for workflow engine errors."""
    pass


class InvalidTransitionError(WorkflowError):
    """Raised when an invalid state transition is attempted."""

    def __init__(self, operation_name: str, from_state: OperationState, to_state: OperationState):
        self.operation_name = operation_name
        self.from_state = from_state
        self.to_state = to_state
        super().__init__(
            f"Invalid transition for '{operation_name}': "
            f"{from_state.value} -> {to_state.value}"
        )


class CycleDetectedError(WorkflowError):
    """Raised when a repeated pattern exceeds the configured cycle limit."""

    def __init__(self, pattern: List[str], repetitions: int):
        self.pattern = pattern
        self.repetitions = repetitions
        super().__init__(
            f"Cycle detected: pattern {pattern} repeated {repetitions} times"
        )


class BudgetExceededError(WorkflowError):
    """Raised when the cumulative cost exceeds the budget."""

    def __init__(self, budget: float, spent: float, operation_name: str):
        self.budget = budget
        self.spent = spent
        self.operation_name = operation_name
        super().__init__(
            f"Budget exceeded after '{operation_name}': "
            f"spent {spent:.2f} of {budget:.2f}"
        )


class DependencyError(WorkflowError):
    """Raised when a dependency cannot be resolved."""

    def __init__(self, operation_name: str, missing: List[str]):
        self.operation_name = operation_name
        self.missing = missing
        super().__init__(
            f"Operation '{operation_name}' depends on unknown operations: {missing}"
        )


class NonRetriableError(WorkflowError):
    """Marks an error that should not be retried."""

    def __init__(self, reason: str):
        self.reason = reason
        super().__init__(f"Non-retriable error: {reason}")


# ===================================================================
# Data Classes
# ===================================================================

@dataclass
class OperationResult:
    """Result returned by an operation handler."""

    success: bool
    cost: float = 0.0
    duration: float = 0.0
    error: Optional[str] = None
    output: Any = None
    attempt_count: int = 1
    metadata: Dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        """Serialize to a plain dictionary."""
        return {
            "success": self.success,
            "cost": self.cost,
            "duration": self.duration,
            "error": self.error,
            "output": str(self.output) if self.output is not None else None,
            "attempt_count": self.attempt_count,
            "metadata": self.metadata,
        }


@dataclass
class LogEntry:
    """A single structured log entry."""

    timestamp: str
    operation: str
    event_type: str
    details: Dict[str, Any] = field(default_factory=dict)
    cost: float = 0.0

    def to_dict(self) -> Dict[str, Any]:
        return {
            "timestamp": self.timestamp,
            "operation": self.operation,
            "event_type": self.event_type,
            "details": self.details,
            "cost": self.cost,
        }

    def to_json(self) -> str:
        return json.dumps(self.to_dict(), default=str)


@dataclass
class WorkflowConfig:
    """Configuration for the workflow engine."""

    max_budget: float = 1000.0
    max_retries: int = 3
    cycle_limit: int = 3
    dry_run: bool = False
    parallel: bool = False
    verbose: bool = False
    max_parallel_workers: int = 4
    backoff_base: float = 0.1
    backoff_max: float = 10.0
    jitter_factor: float = 0.1
    budget_warning_threshold: float = 0.2
    cascade_skip_on_failure: bool = True
    cascade_skip_on_skip: bool = False
    history_window_size: int = 20
    operation_timeout: Optional[float] = None
    strict_transitions: bool = True

    def to_dict(self) -> Dict[str, Any]:
        return {
            "max_budget": self.max_budget,
            "max_retries": self.max_retries,
            "cycle_limit": self.cycle_limit,
            "dry_run": self.dry_run,
            "parallel": self.parallel,
            "verbose": self.verbose,
            "max_parallel_workers": self.max_parallel_workers,
            "backoff_base": self.backoff_base,
            "backoff_max": self.backoff_max,
            "jitter_factor": self.jitter_factor,
            "budget_warning_threshold": self.budget_warning_threshold,
            "cascade_skip_on_failure": self.cascade_skip_on_failure,
            "cascade_skip_on_skip": self.cascade_skip_on_skip,
            "history_window_size": self.history_window_size,
            "operation_timeout": self.operation_timeout,
            "strict_transitions": self.strict_transitions,
        }

    def validate(self) -> List[str]:
        """Return a list of validation errors (empty if valid)."""
        errors: List[str] = []
        if self.max_budget <= 0:
            errors.append("max_budget must be positive")
        if self.max_retries < 1:
            errors.append("max_retries must be >= 1")
        if self.cycle_limit < 1:
            errors.append("cycle_limit must be >= 1")
        if self.max_parallel_workers < 1:
            errors.append("max_parallel_workers must be >= 1")
        if self.backoff_base < 0:
            errors.append("backoff_base must be non-negative")
        if self.backoff_max < self.backoff_base:
            errors.append("backoff_max must be >= backoff_base")
        if not (0 <= self.jitter_factor <= 1):
            errors.append("jitter_factor must be between 0 and 1")
        if not (0 < self.budget_warning_threshold < 1):
            errors.append("budget_warning_threshold must be between 0 and 1")
        if self.history_window_size < 2:
            errors.append("history_window_size must be >= 2")
        return errors


@dataclass
class Operation:
    """Represents a single registerable operation within a workflow."""

    name: str
    handler: Callable
    dependencies: List[str] = field(default_factory=list)
    max_attempts: Optional[int] = None
    estimated_cost: float = 0.0
    timeout: Optional[float] = None
    skip_condition: Optional[Callable] = None
    recovery_handler: Optional[Callable] = None
    tags: Set[str] = field(default_factory=set)
    metadata: Dict[str, Any] = field(default_factory=dict)
    priority: int = 0
    retriable: bool = True

    def __post_init__(self):
        if not self.name:
            raise ValueError("Operation name cannot be empty")
        if self.handler is None:
            raise ValueError(f"Operation '{self.name}' must have a handler")
        if self.max_attempts is not None and self.max_attempts < 1:
            raise ValueError(f"max_attempts for '{self.name}' must be >= 1")
        if self.estimated_cost < 0:
            raise ValueError(f"estimated_cost for '{self.name}' cannot be negative")


@dataclass
class WorkflowResult:
    """Aggregate result of a full workflow run."""

    success: bool
    total_cost: float = 0.0
    total_duration: float = 0.0
    completed_operations: List[str] = field(default_factory=list)
    failed_operations: List[str] = field(default_factory=list)
    skipped_operations: List[str] = field(default_factory=list)
    operation_results: Dict[str, OperationResult] = field(default_factory=dict)
    error: Optional[str] = None
    aborted: bool = False
    abort_reason: Optional[str] = None

    def to_dict(self) -> Dict[str, Any]:
        return {
            "success": self.success,
            "total_cost": self.total_cost,
            "total_duration": self.total_duration,
            "completed_operations": self.completed_operations,
            "failed_operations": self.failed_operations,
            "skipped_operations": self.skipped_operations,
            "operation_results": {
                k: v.to_dict() for k, v in self.operation_results.items()
            },
            "error": self.error,
            "aborted": self.aborted,
            "abort_reason": self.abort_reason,
        }

    def summary(self) -> str:
        """Return a human-readable summary."""
        status = "SUCCESS" if self.success else "FAILED"
        lines = [
            f"Workflow {status}",
            f"  Total cost   : {self.total_cost:.2f}",
            f"  Total duration: {self.total_duration:.4f}s",
            f"  Completed    : {len(self.completed_operations)}",
            f"  Failed       : {len(self.failed_operations)}",
            f"  Skipped      : {len(self.skipped_operations)}",
        ]
        if self.aborted:
            lines.append(f"  Abort reason : {self.abort_reason}")
        return "\n".join(lines)


# ===================================================================
# State Machine
# ===================================================================

class OperationStateMachine:
    """
    Manages state transitions for a single operation.

    Valid transitions:
        PENDING  -> RUNNING
        PENDING  -> SKIPPED
        RUNNING  -> COMPLETED
        RUNNING  -> FAILED
        RUNNING  -> SKIPPED   (e.g., budget exceeded mid-run)
        FAILED   -> RUNNING   (retry)
        FAILED   -> SKIPPED   (give up after max retries, or cascade)

    Invalid examples:
        COMPLETED -> RUNNING  (no re-running completed ops)
        SKIPPED   -> RUNNING  (no re-running skipped ops)
    """

    VALID_TRANSITIONS: Dict[OperationState, Set[OperationState]] = {
        OperationState.PENDING: {
            OperationState.RUNNING,
            OperationState.SKIPPED,
        },
        OperationState.RUNNING: {
            OperationState.COMPLETED,
            OperationState.FAILED,
            OperationState.SKIPPED,
        },
        OperationState.FAILED: {
            OperationState.RUNNING,
            OperationState.SKIPPED,
        },
        OperationState.COMPLETED: set(),
        OperationState.SKIPPED: set(),
    }

    def __init__(self, operation_name: str, strict: bool = True):
        self._name = operation_name
        self._state = OperationState.PENDING
        self._strict = strict
        self._history: List[Tuple[OperationState, OperationState, str]] = []

    @property
    def state(self) -> OperationState:
        return self._state

    @property
    def history(self) -> List[Tuple[OperationState, OperationState, str]]:
        return list(self._history)

    def can_transition(self, to_state: OperationState) -> bool:
        """Check whether a transition from current state to to_state is valid."""
        return to_state in self.VALID_TRANSITIONS.get(self._state, set())

    def transition(self, to_state: OperationState, reason: str = "") -> OperationState:
        """
        Transition to a new state.

        Raises InvalidTransitionError if the transition is not allowed and
        strict mode is enabled.
        """
        if not self.can_transition(to_state):
            if self._strict:
                raise InvalidTransitionError(self._name, self._state, to_state)
            _logger.warning(
                "Ignoring invalid transition for '%s': %s -> %s",
                self._name,
                self._state.value,
                to_state.value,
            )
            return self._state

        old = self._state
        self._state = to_state
        self._history.append((old, to_state, reason))
        return self._state

    def is_terminal(self) -> bool:
        """Return True if the operation is in a terminal state."""
        return self._state in (OperationState.COMPLETED, OperationState.SKIPPED)

    def reset(self) -> None:
        """Reset back to PENDING (used only in testing or special workflows)."""
        self._state = OperationState.PENDING
        self._history.clear()


# ===================================================================
# Dependency Graph & Topological Sort
# ===================================================================

class DependencyGraph:
    """
    Directed acyclic graph for operation dependencies.

    Supports topological sorting, cycle detection within the dependency
    structure, and identification of independent (parallelizable) groups.
    """

    def __init__(self):
        self._adjacency: Dict[str, List[str]] = defaultdict(list)
        self._nodes: Set[str] = set()

    def add_node(self, name: str) -> None:
        self._nodes.add(name)

    def add_edge(self, from_node: str, to_node: str) -> None:
        """Add a dependency edge: from_node depends on to_node."""
        self._nodes.add(from_node)
        self._nodes.add(to_node)
        self._adjacency[from_node].append(to_node)

    def get_dependencies(self, node: str) -> List[str]:
        return list(self._adjacency.get(node, []))

    def get_all_dependencies(self, node: str) -> Set[str]:
        """Return the transitive closure of dependencies for a node."""
        visited: Set[str] = set()
        stack = list(self._adjacency.get(node, []))
        while stack:
            current = stack.pop()
            if current not in visited:
                visited.add(current)
                stack.extend(self._adjacency.get(current, []))
        return visited

    def get_dependents(self, node: str) -> List[str]:
        """Return nodes that depend on the given node."""
        dependents = []
        for n, deps in self._adjacency.items():
            if node in deps:
                dependents.append(n)
        return dependents

    def get_all_dependents(self, node: str) -> Set[str]:
        """Return all transitive dependents of a node."""
        visited: Set[str] = set()
        stack = self.get_dependents(node)
        while stack:
            current = stack.pop()
            if current not in visited:
                visited.add(current)
                stack.extend(self.get_dependents(current))
        return visited

    def detect_cycles(self) -> List[List[str]]:
        """
        Detect all cycles in the dependency graph using DFS.

        Returns a list of cycles, where each cycle is a list of node names.
        """
        cycles: List[List[str]] = []
        visited: Set[str] = set()
        rec_stack: Set[str] = set()
        path: List[str] = []

        def _dfs(node: str) -> None:
            visited.add(node)
            rec_stack.add(node)
            path.append(node)

            for neighbor in self._adjacency.get(node, []):
                if neighbor not in visited:
                    _dfs(neighbor)
                elif neighbor in rec_stack:
                    idx = path.index(neighbor)
                    cycle = path[idx:] + [neighbor]
                    cycles.append(cycle)

            path.pop()
            rec_stack.discard(node)

        for node in self._nodes:
            if node not in visited:
                _dfs(node)

        return cycles

    def topological_sort(self) -> List[str]:
        """
        Return a topological ordering of all nodes.

        Raises WorkflowError if the graph contains a cycle.
        """
        in_degree: Dict[str, int] = {n: 0 for n in self._nodes}
        for node in self._nodes:
            for dep in self._adjacency.get(node, []):
                # node depends on dep, so edge is dep -> node in execution order
                pass

        # Build reverse adjacency for execution ordering
        reverse_adj: Dict[str, List[str]] = defaultdict(list)
        for node, deps in self._adjacency.items():
            for dep in deps:
                reverse_adj[dep].append(node)

        in_degree = {n: 0 for n in self._nodes}
        for node, deps in self._adjacency.items():
            in_degree[node] = len(deps) if node in in_degree else len(deps)

        queue = deque()
        for node in sorted(self._nodes):
            if in_degree.get(node, 0) == 0:
                queue.append(node)

        result: List[str] = []
        while queue:
            node = queue.popleft()
            result.append(node)
            for dependent in sorted(reverse_adj.get(node, [])):
                in_degree[dependent] -= 1
                if in_degree[dependent] == 0:
                    queue.append(dependent)

        if len(result) != len(self._nodes):
            missing = self._nodes - set(result)
            raise WorkflowError(
                f"Dependency cycle detected involving: {sorted(missing)}"
            )

        return result

    def get_parallel_groups(self) -> List[List[str]]:
        """
        Return groups of operations that can be executed in parallel.

        Each group contains operations whose dependencies have all been
        satisfied by previous groups.
        """
        in_degree: Dict[str, int] = {n: 0 for n in self._nodes}
        reverse_adj: Dict[str, List[str]] = defaultdict(list)

        for node, deps in self._adjacency.items():
            in_degree[node] = len(deps)
            for dep in deps:
                reverse_adj[dep].append(node)

        groups: List[List[str]] = []
        remaining = set(self._nodes)

        while remaining:
            # Find all nodes with in_degree 0 among remaining
            ready = sorted([n for n in remaining if in_degree.get(n, 0) == 0])
            if not ready:
                raise WorkflowError(
                    f"Dependency cycle detected involving: {sorted(remaining)}"
                )
            groups.append(ready)
            for node in ready:
                remaining.discard(node)
                for dependent in reverse_adj.get(node, []):
                    in_degree[dependent] -= 1

        return groups

    def __len__(self) -> int:
        return len(self._nodes)

    def __contains__(self, node: str) -> bool:
        return node in self._nodes


# ===================================================================
# Backoff Calculator
# ===================================================================

class BackoffCalculator:
    """
    Calculates exponential backoff with jitter for retry operations.

    The delay for attempt N is:
        base_delay * (2 ** (attempt - 1)) + random_jitter

    Capped at max_delay.
    """

    def __init__(
        self,
        base_delay: float = 0.1,
        max_delay: float = 10.0,
        jitter_factor: float = 0.1,
        seed: Optional[int] = None,
    ):
        self._base = base_delay
        self._max = max_delay
        self._jitter_factor = jitter_factor
        self._rng = random.Random(seed)

    def calculate(self, attempt: int) -> float:
        """Return the delay in seconds for the given attempt number (1-based)."""
        if attempt < 1:
            return 0.0
        raw = self._base * (2 ** (attempt - 1))
        capped = min(raw, self._max)
        jitter = self._rng.uniform(0, self._jitter_factor * capped)
        return capped + jitter

    def calculate_total(self, max_attempts: int) -> float:
        """Return the total maximum delay across all attempts."""
        total = 0.0
        for i in range(1, max_attempts + 1):
            total += self.calculate(i)
        return total

    def reset_seed(self, seed: int) -> None:
        self._rng = random.Random(seed)


# ===================================================================
# Cycle Detector
# ===================================================================

class CycleDetector:
    """
    Detects repeated patterns in the operation execution history.

    Uses a sliding window approach. For each possible pattern length
    (2 to window_size // 2), checks whether the tail of the history
    is a repetition of a shorter pattern.
    """

    def __init__(self, window_size: int = 20, cycle_limit: int = 3):
        self._window_size = window_size
        self._cycle_limit = cycle_limit
        self._history: deque = deque(maxlen=window_size)

    @property
    def history(self) -> List[str]:
        return list(self._history)

    def record(self, operation_name: str) -> None:
        """Record an operation execution."""
        self._history.append(operation_name)

    def check(self) -> Optional[Tuple[List[str], int]]:
        """
        Check for repeated patterns.

        Returns (pattern, repetitions) if a cycle is found, else None.
        """
        history = list(self._history)
        n = len(history)
        if n < 4:
            return None

        # Try pattern lengths from 1 to n//2
        for pat_len in range(1, n // 2 + 1):
            pattern = history[-pat_len:]
            repetitions = 0

            # Count how many times this pattern repeats going backwards
            idx = n - pat_len
            while idx >= pat_len:
                segment = history[idx - pat_len: idx]
                if segment == pattern:
                    repetitions += 1
                    idx -= pat_len
                else:
                    break

            if repetitions >= self._cycle_limit:
                return (pattern, repetitions + 1)  # +1 for the current occurrence

        return None

    def reset(self) -> None:
        self._history.clear()

    def get_fingerprint(self) -> str:
        """Return a hash of the current history for comparison."""
        content = "|".join(self._history)
        return hashlib.md5(content.encode()).hexdigest()


# ===================================================================
# Budget Tracker
# ===================================================================

class BudgetTracker:
    """
    Tracks cumulative spending against a budget.

    Provides warnings when spending approaches the limit and raises
    BudgetExceededError when the budget is fully consumed.
    """

    def __init__(self, max_budget: float, warning_threshold: float = 0.2):
        self._max_budget = max_budget
        self._warning_threshold = warning_threshold
        self._spent = 0.0
        self._history: List[Dict[str, Any]] = []
        self._warnings_issued: Set[str] = set()
        self._lock = threading.Lock()

    @property
    def spent(self) -> float:
        return self._spent

    @property
    def remaining(self) -> float:
        return max(0.0, self._max_budget - self._spent)

    @property
    def utilization(self) -> float:
        """Return the fraction of budget consumed (0.0 to 1.0+)."""
        if self._max_budget <= 0:
            return float("inf")
        return self._spent / self._max_budget

    def record_cost(self, operation_name: str, cost: float) -> None:
        """Record a cost and store in history."""
        with self._lock:
            self._spent += cost
            self._history.append({
                "operation": operation_name,
                "cost": cost,
                "cumulative": self._spent,
                "timestamp": datetime.now(timezone.utc).isoformat(),
            })

    def check_budget(self, operation_name: str = "") -> Dict[str, Any]:
        """
        Check budget status.

        Returns a dict with:
            - exceeded: bool
            - warning: bool
            - remaining: float
            - utilization: float
        """
        remaining = self.remaining
        utilization = self.utilization
        exceeded = self._spent > self._max_budget
        warning = (
            not exceeded
            and remaining < self._max_budget * self._warning_threshold
        )

        return {
            "exceeded": exceeded,
            "warning": warning,
            "remaining": remaining,
            "utilization": utilization,
            "spent": self._spent,
            "budget": self._max_budget,
        }

    def would_exceed(self, estimated_cost: float) -> bool:
        """Check if adding estimated_cost would exceed the budget."""
        return (self._spent + estimated_cost) > self._max_budget

    def get_cost_breakdown(self) -> Dict[str, float]:
        """Return per-operation cost breakdown."""
        breakdown: Dict[str, float] = defaultdict(float)
        for entry in self._history:
            breakdown[entry["operation"]] += entry["cost"]
        return dict(breakdown)

    def get_history(self) -> List[Dict[str, Any]]:
        return list(self._history)

    def reset(self) -> None:
        with self._lock:
            self._spent = 0.0
            self._history.clear()
            self._warnings_issued.clear()


# ===================================================================
# Event Logger
# ===================================================================

class EventLogger:
    """
    Collects structured log entries for all workflow events.

    Thread-safe for use with parallel execution.
    """

    def __init__(self, verbose: bool = False):
        self._entries: List[LogEntry] = []
        self._lock = threading.Lock()
        self._verbose = verbose

    def log(
        self,
        operation: str,
        event_type: str,
        details: Optional[Dict[str, Any]] = None,
        cost: float = 0.0,
    ) -> LogEntry:
        """Create and store a log entry."""
        entry = LogEntry(
            timestamp=datetime.now(timezone.utc).isoformat(),
            operation=operation,
            event_type=event_type,
            details=details or {},
            cost=cost,
        )
        with self._lock:
            self._entries.append(entry)

        if self._verbose:
            _logger.info(
                "[%s] %s: %s (cost=%.2f) %s",
                entry.timestamp,
                operation,
                event_type,
                cost,
                json.dumps(details or {}, default=str),
            )

        return entry

    def get_entries(self) -> List[LogEntry]:
        with self._lock:
            return list(self._entries)

    def get_entries_for_operation(self, operation: str) -> List[LogEntry]:
        with self._lock:
            return [e for e in self._entries if e.operation == operation]

    def get_entries_by_type(self, event_type: str) -> List[LogEntry]:
        with self._lock:
            return [e for e in self._entries if e.event_type == event_type]

    def get_total_cost(self) -> float:
        with self._lock:
            return sum(e.cost for e in self._entries)

    def get_timeline(self) -> List[Dict[str, Any]]:
        """Return entries as a list of dicts, sorted by timestamp."""
        with self._lock:
            sorted_entries = sorted(self._entries, key=lambda e: e.timestamp)
            return [e.to_dict() for e in sorted_entries]

    def filter_entries(
        self,
        operation: Optional[str] = None,
        event_type: Optional[str] = None,
        min_cost: Optional[float] = None,
    ) -> List[LogEntry]:
        """Filter entries by criteria."""
        with self._lock:
            result = list(self._entries)

        if operation is not None:
            result = [e for e in result if e.operation == operation]
        if event_type is not None:
            result = [e for e in result if e.event_type == event_type]
        if min_cost is not None:
            result = [e for e in result if e.cost >= min_cost]

        return result

    def count_by_type(self) -> Dict[str, int]:
        """Return a count of entries grouped by event_type."""
        counts: Dict[str, int] = defaultdict(int)
        with self._lock:
            for entry in self._entries:
                counts[entry.event_type] += 1
        return dict(counts)

    def clear(self) -> None:
        with self._lock:
            self._entries.clear()

    def __len__(self) -> int:
        with self._lock:
            return len(self._entries)

    def export_json(self) -> str:
        """Export all entries as a JSON string."""
        return json.dumps(self.get_timeline(), default=str, indent=2)


# ===================================================================
# Operation Context
# ===================================================================

class OperationContext:
    """
    Provides read-only context information to operation handlers.

    Handlers receive this as their argument and can use it to make
    decisions based on workflow state.
    """

    def __init__(
        self,
        operation_name: str,
        attempt: int,
        total_attempts: int,
        budget_remaining: float,
        budget_utilization: float,
        completed_operations: List[str],
        failed_operations: List[str],
        shared_data: Dict[str, Any],
        dry_run: bool = False,
    ):
        self.operation_name = operation_name
        self.attempt = attempt
        self.total_attempts = total_attempts
        self.budget_remaining = budget_remaining
        self.budget_utilization = budget_utilization
        self.completed_operations = list(completed_operations)
        self.failed_operations = list(failed_operations)
        self.shared_data = shared_data
        self.dry_run = dry_run

    def is_first_attempt(self) -> bool:
        return self.attempt == 1

    def is_last_attempt(self) -> bool:
        return self.attempt >= self.total_attempts

    def has_budget(self, required: float = 0.0) -> bool:
        return self.budget_remaining > required

    def get_shared(self, key: str, default: Any = None) -> Any:
        return self.shared_data.get(key, default)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "operation_name": self.operation_name,
            "attempt": self.attempt,
            "total_attempts": self.total_attempts,
            "budget_remaining": self.budget_remaining,
            "budget_utilization": self.budget_utilization,
            "completed_operations": self.completed_operations,
            "failed_operations": self.failed_operations,
            "dry_run": self.dry_run,
        }


# ===================================================================
# Workflow Validator
# ===================================================================

class WorkflowValidator:
    """
    Validates a workflow configuration and set of operations before execution.

    Checks for common errors like missing dependencies, duplicate names,
    impossible budgets, and dependency cycles.
    """

    def __init__(self):
        self._errors: List[str] = []
        self._warnings: List[str] = []

    @property
    def errors(self) -> List[str]:
        return list(self._errors)

    @property
    def warnings(self) -> List[str]:
        return list(self._warnings)

    @property
    def is_valid(self) -> bool:
        return len(self._errors) == 0

    def validate(
        self,
        config: WorkflowConfig,
        operations: Dict[str, Operation],
    ) -> bool:
        """Run all validation checks. Return True if valid."""
        self._errors.clear()
        self._warnings.clear()

        self._validate_config(config)
        self._validate_operations(operations)
        self._validate_dependencies(operations)
        self._validate_budget_feasibility(config, operations)
        self._validate_dependency_cycles(operations)

        return self.is_valid

    def _validate_config(self, config: WorkflowConfig) -> None:
        config_errors = config.validate()
        self._errors.extend(config_errors)

    def _validate_operations(self, operations: Dict[str, Operation]) -> None:
        if not operations:
            self._errors.append("Workflow has no operations")
            return

        for name, op in operations.items():
            if name != op.name:
                self._errors.append(
                    f"Operation key '{name}' doesn't match operation name '{op.name}'"
                )
            if op.handler is None:
                self._errors.append(f"Operation '{name}' has no handler")
            if op.estimated_cost < 0:
                self._errors.append(
                    f"Operation '{name}' has negative estimated_cost"
                )

    def _validate_dependencies(self, operations: Dict[str, Operation]) -> None:
        known_names = set(operations.keys())
        for name, op in operations.items():
            missing = [d for d in op.dependencies if d not in known_names]
            if missing:
                self._errors.append(
                    f"Operation '{name}' depends on unknown operations: {missing}"
                )
            if name in op.dependencies:
                self._errors.append(f"Operation '{name}' depends on itself")

    def _validate_budget_feasibility(
        self, config: WorkflowConfig, operations: Dict[str, Operation]
    ) -> None:
        total_estimated = sum(op.estimated_cost for op in operations.values())
        if total_estimated > config.max_budget:
            self._warnings.append(
                f"Total estimated cost ({total_estimated:.2f}) exceeds "
                f"budget ({config.max_budget:.2f})"
            )

    def _validate_dependency_cycles(self, operations: Dict[str, Operation]) -> None:
        graph = DependencyGraph()
        for name, op in operations.items():
            graph.add_node(name)
            for dep in op.dependencies:
                graph.add_edge(name, dep)

        cycles = graph.detect_cycles()
        if cycles:
            for cycle in cycles:
                self._errors.append(
                    f"Dependency cycle detected: {' -> '.join(cycle)}"
                )

    def get_report(self) -> str:
        lines = ["Workflow Validation Report", "=" * 40]
        if self._errors:
            lines.append(f"\nErrors ({len(self._errors)}):")
            for err in self._errors:
                lines.append(f"  - {err}")
        if self._warnings:
            lines.append(f"\nWarnings ({len(self._warnings)}):")
            for warn in self._warnings:
                lines.append(f"  - {warn}")
        if self.is_valid:
            lines.append("\nResult: VALID")
        else:
            lines.append("\nResult: INVALID")
        return "\n".join(lines)


# ===================================================================
# Workflow Statistics
# ===================================================================

class WorkflowStatistics:
    """
    Collects and computes statistics about a workflow execution.
    """

    def __init__(self):
        self._operation_durations: Dict[str, List[float]] = defaultdict(list)
        self._operation_costs: Dict[str, List[float]] = defaultdict(list)
        self._retry_counts: Dict[str, int] = defaultdict(int)
        self._state_transitions: Dict[str, List[Tuple[str, str]]] = defaultdict(list)

    def record_duration(self, operation: str, duration: float) -> None:
        self._operation_durations[operation].append(duration)

    def record_cost(self, operation: str, cost: float) -> None:
        self._operation_costs[operation].append(cost)

    def record_retry(self, operation: str) -> None:
        self._retry_counts[operation] += 1

    def record_transition(
        self, operation: str, from_state: str, to_state: str
    ) -> None:
        self._state_transitions[operation].append((from_state, to_state))

    def get_average_duration(self, operation: Optional[str] = None) -> float:
        if operation:
            durations = self._operation_durations.get(operation, [])
        else:
            durations = [d for dlist in self._operation_durations.values() for d in dlist]
        if not durations:
            return 0.0
        return sum(durations) / len(durations)

    def get_total_cost(self) -> float:
        return sum(
            c for clist in self._operation_costs.values() for c in clist
        )

    def get_max_duration(self) -> Tuple[str, float]:
        max_op = ""
        max_dur = 0.0
        for op, durations in self._operation_durations.items():
            for d in durations:
                if d > max_dur:
                    max_dur = d
                    max_op = op
        return max_op, max_dur

    def get_retry_summary(self) -> Dict[str, int]:
        return dict(self._retry_counts)

    def get_cost_breakdown(self) -> Dict[str, float]:
        return {
            op: sum(costs) for op, costs in self._operation_costs.items()
        }

    def get_percentile_duration(self, percentile: float) -> float:
        """Compute the given percentile (0-100) across all durations."""
        all_durations = sorted(
            d for dlist in self._operation_durations.values() for d in dlist
        )
        if not all_durations:
            return 0.0
        idx = int(len(all_durations) * percentile / 100)
        idx = min(idx, len(all_durations) - 1)
        return all_durations[idx]

    def get_summary(self) -> Dict[str, Any]:
        return {
            "total_operations": len(self._operation_durations),
            "total_cost": self.get_total_cost(),
            "average_duration": self.get_average_duration(),
            "max_duration": self.get_max_duration(),
            "retry_summary": self.get_retry_summary(),
            "cost_breakdown": self.get_cost_breakdown(),
            "p50_duration": self.get_percentile_duration(50),
            "p95_duration": self.get_percentile_duration(95),
            "p99_duration": self.get_percentile_duration(99),
        }


# ===================================================================
# Operation Registry
# ===================================================================

class OperationRegistry:
    """
    Registry for managing operations.

    Provides lookup by name, tag, and dependency traversal.
    """

    def __init__(self):
        self._operations: Dict[str, Operation] = {}
        self._tag_index: Dict[str, Set[str]] = defaultdict(set)

    def register(self, operation: Operation) -> None:
        """Register an operation. Raises ValueError if name already exists."""
        if operation.name in self._operations:
            raise ValueError(
                f"Operation '{operation.name}' is already registered"
            )
        self._operations[operation.name] = operation
        for tag in operation.tags:
            self._tag_index[tag].add(operation.name)

    def unregister(self, name: str) -> Optional[Operation]:
        """Remove and return an operation by name."""
        op = self._operations.pop(name, None)
        if op:
            for tag in op.tags:
                self._tag_index[tag].discard(name)
        return op

    def get(self, name: str) -> Optional[Operation]:
        return self._operations.get(name)

    def get_all(self) -> Dict[str, Operation]:
        return dict(self._operations)

    def get_by_tag(self, tag: str) -> List[Operation]:
        names = self._tag_index.get(tag, set())
        return [self._operations[n] for n in names if n in self._operations]

    def get_names(self) -> List[str]:
        return list(self._operations.keys())

    def has(self, name: str) -> bool:
        return name in self._operations

    def count(self) -> int:
        return len(self._operations)

    def clear(self) -> None:
        self._operations.clear()
        self._tag_index.clear()

    def get_dependency_chain(self, name: str) -> List[str]:
        """Return the full dependency chain for an operation (BFS order)."""
        if name not in self._operations:
            return []
        visited: Set[str] = set()
        queue = deque([name])
        chain: List[str] = []

        while queue:
            current = queue.popleft()
            if current in visited:
                continue
            visited.add(current)
            if current != name:
                chain.append(current)
            op = self._operations.get(current)
            if op:
                for dep in op.dependencies:
                    if dep not in visited:
                        queue.append(dep)

        return chain

    def build_dependency_graph(self) -> DependencyGraph:
        """Build a DependencyGraph from all registered operations."""
        graph = DependencyGraph()
        for name, op in self._operations.items():
            graph.add_node(name)
            for dep in op.dependencies:
                graph.add_edge(name, dep)
        return graph

    def validate_dependencies(self) -> List[str]:
        """Return a list of missing dependency names."""
        known = set(self._operations.keys())
        missing = []
        for name, op in self._operations.items():
            for dep in op.dependencies:
                if dep not in known:
                    missing.append(dep)
        return missing


# ===================================================================
# Parallel Executor
# ===================================================================

class ParallelExecutor:
    """
    Executes a batch of operations in parallel using threads.

    Collects results and handles per-operation failures without
    killing the entire batch.
    """

    def __init__(self, max_workers: int = 4):
        self._max_workers = max_workers

    def execute_batch(
        self,
        operations: List[Tuple[str, Callable]],
        timeout: Optional[float] = None,
    ) -> Dict[str, Any]:
        """
        Execute a batch of (name, callable) pairs in parallel.

        Returns a dict mapping operation name to its result or exception.
        """
        results: Dict[str, Any] = {}
        errors: Dict[str, str] = {}

        if not operations:
            return results

        with ThreadPoolExecutor(max_workers=self._max_workers) as executor:
            future_to_name: Dict[Future, str] = {}
            for name, fn in operations:
                future = executor.submit(fn)
                future_to_name[future] = name

            for future in as_completed(future_to_name, timeout=timeout):
                name = future_to_name[future]
                try:
                    result = future.result()
                    results[name] = result
                except Exception as e:
                    results[name] = OperationResult(
                        success=False,
                        error=str(e),
                        duration=0.0,
                    )
                    errors[name] = str(e)

        return results

    def execute_with_callbacks(
        self,
        operations: List[Tuple[str, Callable]],
        on_complete: Optional[Callable] = None,
        on_error: Optional[Callable] = None,
        timeout: Optional[float] = None,
    ) -> Dict[str, Any]:
        """
        Execute operations in parallel with per-operation callbacks.
        """
        results: Dict[str, Any] = {}

        if not operations:
            return results

        with ThreadPoolExecutor(max_workers=self._max_workers) as executor:
            future_to_name: Dict[Future, str] = {}
            for name, fn in operations:
                future = executor.submit(fn)
                future_to_name[future] = name

            for future in as_completed(future_to_name, timeout=timeout):
                name = future_to_name[future]
                try:
                    result = future.result()
                    results[name] = result
                    if on_complete:
                        on_complete(name, result)
                except Exception as e:
                    error_result = OperationResult(
                        success=False,
                        error=str(e),
                        duration=0.0,
                    )
                    results[name] = error_result
                    if on_error:
                        on_error(name, e)

        return results


# ===================================================================
# Recovery Manager
# ===================================================================

class RecoveryManager:
    """
    Manages error recovery for failed operations.

    When an operation fails, the recovery manager checks for a registered
    recovery handler and attempts to execute it before marking the
    operation as permanently failed.
    """

    def __init__(self, logger: EventLogger):
        self._recovery_handlers: Dict[str, Callable] = {}
        self._logger = logger
        self._recovery_history: List[Dict[str, Any]] = []

    def register_handler(self, operation_name: str, handler: Callable) -> None:
        """Register a recovery handler for an operation."""
        self._recovery_handlers[operation_name] = handler

    def has_handler(self, operation_name: str) -> bool:
        return operation_name in self._recovery_handlers

    def attempt_recovery(
        self,
        operation_name: str,
        error: str,
        context: OperationContext,
    ) -> Optional[OperationResult]:
        """
        Attempt to recover from a failure.

        Returns an OperationResult if recovery succeeds, None otherwise.
        """
        handler = self._recovery_handlers.get(operation_name)
        if handler is None:
            return None

        self._logger.log(
            operation_name,
            EventType.RECOVERY_ATTEMPT.value,
            {"original_error": error},
        )

        try:
            result = handler(context, error)
            if isinstance(result, OperationResult) and result.success:
                self._logger.log(
                    operation_name,
                    EventType.RECOVERY_SUCCESS.value,
                    {"original_error": error, "recovery_output": str(result.output)},
                )
                self._recovery_history.append({
                    "operation": operation_name,
                    "original_error": error,
                    "success": True,
                    "timestamp": datetime.now(timezone.utc).isoformat(),
                })
                return result
            else:
                self._logger.log(
                    operation_name,
                    EventType.RECOVERY_FAILED.value,
                    {"original_error": error, "recovery_error": "handler returned failure"},
                )
                self._recovery_history.append({
                    "operation": operation_name,
                    "original_error": error,
                    "success": False,
                    "timestamp": datetime.now(timezone.utc).isoformat(),
                })
                return None
        except Exception as recovery_error:
            self._logger.log(
                operation_name,
                EventType.RECOVERY_FAILED.value,
                {"original_error": error, "recovery_error": str(recovery_error)},
            )
            self._recovery_history.append({
                "operation": operation_name,
                "original_error": error,
                "success": False,
                "recovery_error": str(recovery_error),
                "timestamp": datetime.now(timezone.utc).isoformat(),
            })
            return None

    def get_recovery_history(self) -> List[Dict[str, Any]]:
        return list(self._recovery_history)

    def get_success_rate(self) -> float:
        if not self._recovery_history:
            return 0.0
        successes = sum(1 for h in self._recovery_history if h["success"])
        return successes / len(self._recovery_history)


# ===================================================================
# Skip Evaluator
# ===================================================================

class SkipEvaluator:
    """
    Evaluates whether operations should be skipped.

    Handles both explicit skip conditions and cascade skipping
    (when a dependency fails or is skipped).
    """

    def __init__(
        self,
        cascade_on_failure: bool = True,
        cascade_on_skip: bool = False,
    ):
        self._cascade_on_failure = cascade_on_failure
        self._cascade_on_skip = cascade_on_skip

    def should_skip(
        self,
        operation: Operation,
        context: OperationContext,
        dependency_states: Dict[str, OperationState],
    ) -> Tuple[bool, str]:
        """
        Determine if an operation should be skipped.

        Returns (should_skip, reason).
        """
        # Check explicit skip condition first
        if operation.skip_condition is not None:
            try:
                if operation.skip_condition(context):
                    return True, "skip_condition returned True"
            except Exception as e:
                return True, f"skip_condition raised error: {e}"

        # Check cascade from dependencies
        for dep_name in operation.dependencies:
            dep_state = dependency_states.get(dep_name)

            if dep_state == OperationState.FAILED and self._cascade_on_failure:
                return True, f"dependency '{dep_name}' failed"

            if dep_state == OperationState.SKIPPED and self._cascade_on_skip:
                return True, f"dependency '{dep_name}' was skipped"

            # If a dependency hasn't completed, skip
            if dep_state not in (
                OperationState.COMPLETED,
                OperationState.FAILED,
                OperationState.SKIPPED,
            ):
                if dep_state is not None:
                    return True, f"dependency '{dep_name}' in state {dep_state.value}"

        return False, ""

    def evaluate_cascade(
        self,
        failed_operation: str,
        all_operations: Dict[str, Operation],
        dependency_graph: DependencyGraph,
    ) -> List[str]:
        """
        Given a failed operation, return the list of operations that
        should be cascade-skipped.
        """
        if not self._cascade_on_failure:
            return []

        return sorted(dependency_graph.get_all_dependents(failed_operation))


# ===================================================================
# Workflow Engine (Main Orchestrator)
# ===================================================================

class WorkflowEngine:
    """
    The main workflow orchestrator.

    Coordinates operation execution with dependency resolution, retries,
    budget tracking, cycle detection, parallel execution, and logging.
    """

    def __init__(self, config: Optional[WorkflowConfig] = None):
        self._config = config or WorkflowConfig()
        self._registry = OperationRegistry()
        self._logger = EventLogger(verbose=self._config.verbose)
        self._budget = BudgetTracker(
            max_budget=self._config.max_budget,
            warning_threshold=self._config.budget_warning_threshold,
        )
        self._cycle_detector = CycleDetector(
            window_size=self._config.history_window_size,
            cycle_limit=self._config.cycle_limit,
        )
        self._backoff = BackoffCalculator(
            base_delay=self._config.backoff_base,
            max_delay=self._config.backoff_max,
            jitter_factor=self._config.jitter_factor,
        )
        self._recovery = RecoveryManager(self._logger)
        self._skip_evaluator = SkipEvaluator(
            cascade_on_failure=self._config.cascade_skip_on_failure,
            cascade_on_skip=self._config.cascade_skip_on_skip,
        )
        self._parallel_executor = ParallelExecutor(
            max_workers=self._config.max_parallel_workers,
        )
        self._validator = WorkflowValidator()
        self._statistics = WorkflowStatistics()

        # Runtime state
        self._state_machines: Dict[str, OperationStateMachine] = {}
        self._operation_results: Dict[str, OperationResult] = {}
        self._shared_data: Dict[str, Any] = {}
        self._execution_order: List[str] = []
        self._completed: List[str] = []
        self._failed: List[str] = []
        self._skipped: List[str] = []
        self._running = False
        self._aborted = False
        self._abort_reason: Optional[str] = None
        self._start_time: Optional[float] = None
        self._lock = threading.Lock()

    # ----- Properties -----

    @property
    def config(self) -> WorkflowConfig:
        return self._config

    @property
    def is_running(self) -> bool:
        return self._running

    @property
    def operations(self) -> Dict[str, Operation]:
        return self._registry.get_all()

    @property
    def operation_count(self) -> int:
        return self._registry.count()

    @property
    def total_spent(self) -> float:
        return self._budget.spent

    @property
    def budget_remaining(self) -> float:
        return self._budget.remaining

    # ----- Operation Registration -----

    def add_operation(
        self,
        name: str,
        handler: Callable,
        dependencies: Optional[List[str]] = None,
        max_attempts: Optional[int] = None,
        estimated_cost: float = 0.0,
        timeout: Optional[float] = None,
        skip_condition: Optional[Callable] = None,
        recovery_handler: Optional[Callable] = None,
        tags: Optional[Set[str]] = None,
        metadata: Optional[Dict[str, Any]] = None,
        priority: int = 0,
        retriable: bool = True,
    ) -> None:
        """
        Register a new operation in the workflow.

        Parameters
        ----------
        name : str
            Unique name for the operation.
        handler : callable
            Function that takes an OperationContext and returns OperationResult.
        dependencies : list of str, optional
            Names of operations that must complete before this one.
        max_attempts : int, optional
            Override global max_retries for this operation.
        estimated_cost : float
            Estimated cost for budget planning.
        timeout : float, optional
            Per-operation timeout in seconds.
        skip_condition : callable, optional
            Function that takes context and returns bool (True = skip).
        recovery_handler : callable, optional
            Function that takes (context, error_str) and returns OperationResult.
        tags : set of str, optional
            Tags for filtering and grouping.
        metadata : dict, optional
            Arbitrary metadata.
        priority : int
            Priority for ordering (higher = runs first among peers).
        retriable : bool
            Whether this operation can be retried on failure.
        """
        operation = Operation(
            name=name,
            handler=handler,
            dependencies=dependencies or [],
            max_attempts=max_attempts,
            estimated_cost=estimated_cost,
            timeout=timeout or self._config.operation_timeout,
            skip_condition=skip_condition,
            recovery_handler=recovery_handler,
            tags=tags or set(),
            metadata=metadata or {},
            priority=priority,
            retriable=retriable,
        )

        self._registry.register(operation)
        self._state_machines[name] = OperationStateMachine(
            name, strict=self._config.strict_transitions
        )

        if recovery_handler is not None:
            self._recovery.register_handler(name, recovery_handler)

    def remove_operation(self, name: str) -> bool:
        """Remove a registered operation. Returns True if it existed."""
        op = self._registry.unregister(name)
        if op:
            self._state_machines.pop(name, None)
            return True
        return False

    # ----- Workflow Execution -----

    def run(self) -> WorkflowResult:
        """
        Execute the full workflow.

        Returns a WorkflowResult summarizing the outcome.
        """
        self._start_time = time.monotonic()
        self._running = True
        self._aborted = False
        self._abort_reason = None
        self._completed.clear()
        self._failed.clear()
        self._skipped.clear()
        self._operation_results.clear()
        self._cycle_detector.reset()

        self._logger.log("workflow", EventType.WORKFLOW_START.value, {
            "operation_count": self._registry.count(),
            "config": self._config.to_dict(),
        })

        # Validate
        all_ops = self._registry.get_all()
        if not self._validator.validate(self._config, all_ops):
            error_msg = "; ".join(self._validator.errors)
            self._logger.log(
                "workflow",
                EventType.WORKFLOW_FAILED.value,
                {"reason": "validation_failed", "errors": self._validator.errors},
            )
            self._running = False
            return WorkflowResult(
                success=False,
                error=f"Validation failed: {error_msg}",
                total_duration=time.monotonic() - self._start_time,
            )

        # Build execution plan
        try:
            if self._config.parallel:
                result = self._run_parallel_workflow(all_ops)
            else:
                result = self._run_sequential_workflow(all_ops)
        except CycleDetectedError as e:
            self._logger.log("workflow", EventType.WORKFLOW_FAILED.value, {
                "reason": "cycle_detected",
                "pattern": e.pattern,
                "repetitions": e.repetitions,
            })
            result = WorkflowResult(
                success=False,
                error=str(e),
                total_cost=self._budget.spent,
                total_duration=time.monotonic() - self._start_time,
                completed_operations=list(self._completed),
                failed_operations=list(self._failed),
                skipped_operations=list(self._skipped),
                operation_results=dict(self._operation_results),
                aborted=True,
                abort_reason="cycle_detected",
            )
        except BudgetExceededError as e:
            self._logger.log("workflow", EventType.WORKFLOW_FAILED.value, {
                "reason": "budget_exceeded",
                "budget": e.budget,
                "spent": e.spent,
            })
            result = WorkflowResult(
                success=False,
                error=str(e),
                total_cost=self._budget.spent,
                total_duration=time.monotonic() - self._start_time,
                completed_operations=list(self._completed),
                failed_operations=list(self._failed),
                skipped_operations=list(self._skipped),
                operation_results=dict(self._operation_results),
                aborted=True,
                abort_reason="budget_exceeded",
            )
        except Exception as e:
            self._logger.log("workflow", EventType.WORKFLOW_FAILED.value, {
                "reason": "unexpected_error",
                "error": str(e),
                "traceback": traceback.format_exc(),
            })
            result = WorkflowResult(
                success=False,
                error=str(e),
                total_cost=self._budget.spent,
                total_duration=time.monotonic() - self._start_time,
                completed_operations=list(self._completed),
                failed_operations=list(self._failed),
                skipped_operations=list(self._skipped),
                operation_results=dict(self._operation_results),
            )

        self._running = False

        # Final log
        event_type = (
            EventType.WORKFLOW_COMPLETE.value
            if result.success
            else EventType.WORKFLOW_FAILED.value
        )
        self._logger.log("workflow", event_type, result.to_dict())

        return result

    def _run_sequential_workflow(
        self, all_ops: Dict[str, Operation]
    ) -> WorkflowResult:
        """Execute operations in topological order, one at a time."""
        graph = self._registry.build_dependency_graph()
        try:
            execution_order = graph.topological_sort()
        except WorkflowError:
            raise

        self._execution_order = execution_order

        for op_name in execution_order:
            if self._aborted:
                break

            operation = all_ops[op_name]
            sm = self._state_machines[op_name]

            # Check budget before starting
            budget_status = self._budget.check_budget(op_name)
            if budget_status["exceeded"]:
                self._handle_budget_exceeded(op_name)
                break

            if budget_status["warning"]:
                self._logger.log(
                    op_name,
                    EventType.BUDGET_WARNING.value,
                    budget_status,
                )

            # Check skip conditions
            dep_states = self._get_dependency_states()
            context = self._build_context(op_name, attempt=1)
            should_skip, skip_reason = self._skip_evaluator.should_skip(
                operation, context, dep_states
            )

            if should_skip:
                self._mark_skipped(op_name, skip_reason)
                continue

            # Execute the operation (with retries)
            result = self._execute_with_retries(operation)
            self._operation_results[op_name] = result

            if result.success:
                self._mark_completed(op_name, result)
            else:
                self._mark_failed(op_name, result)
                # Cascade skip dependents
                if self._config.cascade_skip_on_failure:
                    dependents = self._skip_evaluator.evaluate_cascade(
                        op_name, all_ops, graph
                    )
                    for dep_name in dependents:
                        if dep_name not in self._completed and dep_name not in self._failed:
                            self._mark_skipped(
                                dep_name,
                                f"cascade from failed '{op_name}'",
                            )

            # Check for execution cycles
            self._cycle_detector.record(op_name)
            cycle = self._cycle_detector.check()
            if cycle:
                pattern, reps = cycle
                self._logger.log(
                    op_name,
                    EventType.CYCLE_DETECTED.value,
                    {"pattern": pattern, "repetitions": reps},
                )
                raise CycleDetectedError(pattern, reps)

        return self._build_result()

    def _run_parallel_workflow(
        self, all_ops: Dict[str, Operation]
    ) -> WorkflowResult:
        """Execute operations in parallel groups based on dependency layers."""
        graph = self._registry.build_dependency_graph()
        try:
            groups = graph.get_parallel_groups()
        except WorkflowError:
            raise

        self._execution_order = [op for group in groups for op in group]

        for group_idx, group in enumerate(groups):
            if self._aborted:
                break

            # Filter out already-skipped operations
            active_ops = [
                name for name in group
                if name not in self._skipped
                and name not in self._completed
                and name not in self._failed
            ]

            if not active_ops:
                continue

            # Check budget
            budget_status = self._budget.check_budget()
            if budget_status["exceeded"]:
                for name in active_ops:
                    self._mark_skipped(name, "budget_exceeded")
                break

            if budget_status["warning"]:
                self._logger.log(
                    "workflow",
                    EventType.BUDGET_WARNING.value,
                    {**budget_status, "group_index": group_idx},
                )

            self._logger.log(
                "workflow",
                EventType.PARALLEL_BATCH_START.value,
                {"group_index": group_idx, "operations": active_ops},
            )

            if len(active_ops) == 1:
                # Single operation, no need for threads
                self._execute_single_in_group(active_ops[0], all_ops, graph)
            else:
                self._execute_parallel_group(active_ops, all_ops, graph)

            self._logger.log(
                "workflow",
                EventType.PARALLEL_BATCH_COMPLETE.value,
                {"group_index": group_idx},
            )

            # Record history for cycle detection
            for name in active_ops:
                self._cycle_detector.record(name)

            cycle = self._cycle_detector.check()
            if cycle:
                pattern, reps = cycle
                raise CycleDetectedError(pattern, reps)

        return self._build_result()

    def _execute_single_in_group(
        self,
        op_name: str,
        all_ops: Dict[str, Operation],
        graph: DependencyGraph,
    ) -> None:
        """Execute a single operation within a parallel group context."""
        operation = all_ops[op_name]
        dep_states = self._get_dependency_states()
        context = self._build_context(op_name, attempt=1)

        should_skip, skip_reason = self._skip_evaluator.should_skip(
            operation, context, dep_states
        )
        if should_skip:
            self._mark_skipped(op_name, skip_reason)
            return

        result = self._execute_with_retries(operation)
        self._operation_results[op_name] = result

        if result.success:
            self._mark_completed(op_name, result)
        else:
            self._mark_failed(op_name, result)
            if self._config.cascade_skip_on_failure:
                dependents = self._skip_evaluator.evaluate_cascade(
                    op_name, all_ops, graph
                )
                for dep_name in dependents:
                    if dep_name not in self._completed and dep_name not in self._failed:
                        self._mark_skipped(dep_name, f"cascade from failed '{op_name}'")

    def _execute_parallel_group(
        self,
        op_names: List[str],
        all_ops: Dict[str, Operation],
        graph: DependencyGraph,
    ) -> None:
        """Execute a group of operations in parallel."""
        # Pre-check skip conditions
        to_execute: List[str] = []
        for name in op_names:
            operation = all_ops[name]
            dep_states = self._get_dependency_states()
            context = self._build_context(name, attempt=1)
            should_skip, skip_reason = self._skip_evaluator.should_skip(
                operation, context, dep_states
            )
            if should_skip:
                self._mark_skipped(name, skip_reason)
            else:
                to_execute.append(name)

        if not to_execute:
            return

        # Build callable pairs
        def make_executor(op_name: str) -> Callable:
            def _exec():
                return self._execute_with_retries(all_ops[op_name])
            return _exec

        batch = [(name, make_executor(name)) for name in to_execute]
        results = self._parallel_executor.execute_batch(
            batch,
            timeout=self._config.operation_timeout,
        )

        # Process results
        for name in to_execute:
            result = results.get(name)
            if result is None:
                result = OperationResult(
                    success=False,
                    error="No result returned from parallel execution",
                )

            with self._lock:
                self._operation_results[name] = result

            if result.success:
                self._mark_completed(name, result)
            else:
                self._mark_failed(name, result)
                if self._config.cascade_skip_on_failure:
                    dependents = self._skip_evaluator.evaluate_cascade(
                        name, all_ops, graph
                    )
                    for dep_name in dependents:
                        if dep_name not in self._completed and dep_name not in self._failed:
                            self._mark_skipped(
                                dep_name, f"cascade from failed '{name}'"
                            )

    # ----- Operation Execution with Retries -----

    def _execute_with_retries(self, operation: Operation) -> OperationResult:
        """
        Execute an operation, retrying on failure up to max_attempts.

        Uses exponential backoff between retries.
        """
        max_attempts = operation.max_attempts or self._config.max_retries
        last_result: Optional[OperationResult] = None

        for attempt in range(1, max_attempts + 1):
            # Transition to RUNNING
            sm = self._state_machines[operation.name]
            if sm.can_transition(OperationState.RUNNING):
                sm.transition(OperationState.RUNNING, f"attempt {attempt}")
                self._statistics.record_transition(
                    operation.name,
                    sm.history[-1][0].value if sm.history else "pending",
                    "running",
                )

            context = self._build_context(operation.name, attempt, max_attempts)

            self._logger.log(
                operation.name,
                EventType.OPERATION_START.value,
                {"attempt": attempt, "max_attempts": max_attempts},
            )

            start_time = time.monotonic()

            try:
                result = self._invoke_handler(operation, context)
            except NonRetriableError as e:
                duration = time.monotonic() - start_time
                result = OperationResult(
                    success=False,
                    error=str(e),
                    duration=duration,
                    attempt_count=attempt,
                )
                # Non-retriable: transition to FAILED immediately
                self._record_operation_cost(operation.name, result)
                self._statistics.record_duration(operation.name, duration)
                if sm.can_transition(OperationState.FAILED):
                    sm.transition(OperationState.FAILED, f"non-retriable: {e}")
                return result
            except Exception as e:
                duration = time.monotonic() - start_time
                result = OperationResult(
                    success=False,
                    error=str(e),
                    duration=duration,
                    attempt_count=attempt,
                )

            duration = time.monotonic() - start_time
            result.duration = duration
            result.attempt_count = attempt
            last_result = result

            self._statistics.record_duration(operation.name, duration)

            if result.success:
                self._record_operation_cost(operation.name, result)
                if sm.can_transition(OperationState.COMPLETED):
                    sm.transition(OperationState.COMPLETED, f"attempt {attempt}")
                return result

            # Record cost even on failure
            self._record_operation_cost(operation.name, result)

            self._logger.log(
                operation.name,
                EventType.OPERATION_FAILED.value,
                {
                    "attempt": attempt,
                    "error": result.error,
                    "cost": result.cost,
                },
                cost=result.cost,
            )

            # Attempt recovery
            if self._recovery.has_handler(operation.name):
                recovery_result = self._recovery.attempt_recovery(
                    operation.name, result.error or "", context
                )
                if recovery_result is not None:
                    recovery_result.attempt_count = attempt
                    self._record_operation_cost(operation.name, recovery_result)
                    if sm.can_transition(OperationState.COMPLETED):
                        sm.transition(OperationState.COMPLETED, "recovered")
                    return recovery_result

            # Check if we should retry
            if attempt < max_attempts:
                if not operation.retriable:
                    if sm.can_transition(OperationState.FAILED):
                        sm.transition(OperationState.FAILED, "not retriable")
                    return result

                # Check budget before retrying
                budget_status = self._budget.check_budget(operation.name)
                if budget_status["exceeded"]:
                    if sm.can_transition(OperationState.FAILED):
                        sm.transition(OperationState.FAILED, "budget exceeded during retry")
                    return result

                # Backoff before retry
                delay = self._backoff.calculate(attempt)
                self._logger.log(
                    operation.name,
                    EventType.OPERATION_RETRY.value,
                    {
                        "attempt": attempt,
                        "next_attempt": attempt + 1,
                        "delay": delay,
                    },
                )
                self._statistics.record_retry(operation.name)

                time.sleep(delay)

                # Transition back to RUNNING for retry
                if sm.can_transition(OperationState.RUNNING):
                    sm.transition(OperationState.RUNNING, f"retry attempt {attempt + 1}")
                elif sm.state == OperationState.RUNNING:
                    # Already running, need to go to FAILED first then RUNNING
                    if sm.can_transition(OperationState.FAILED):
                        sm.transition(OperationState.FAILED, f"attempt {attempt} failed")
                    if sm.can_transition(OperationState.RUNNING):
                        sm.transition(OperationState.RUNNING, f"retry attempt {attempt + 1}")

        # All attempts exhausted
        if sm.can_transition(OperationState.FAILED):
            sm.transition(OperationState.FAILED, "max attempts exhausted")

        return last_result or OperationResult(
            success=False,
            error="All attempts exhausted",
            attempt_count=max_attempts,
        )

    def _invoke_handler(
        self, operation: Operation, context: OperationContext
    ) -> OperationResult:
        """
        Invoke the operation handler with timeout support.

        If the operation has a timeout, run it in a thread and
        cancel if it exceeds the limit.
        """
        if operation.timeout is not None and operation.timeout > 0:
            return self._invoke_with_timeout(operation, context, operation.timeout)
        return self._invoke_direct(operation, context)

    def _invoke_direct(
        self, operation: Operation, context: OperationContext
    ) -> OperationResult:
        """Invoke the handler directly."""
        try:
            result = operation.handler(context)
            if not isinstance(result, OperationResult):
                # If handler returns something else, wrap it
                return OperationResult(
                    success=True,
                    output=result,
                )
            return result
        except NonRetriableError:
            raise
        except Exception as e:
            return OperationResult(
                success=False,
                error=f"{type(e).__name__}: {str(e)}",
            )

    def _invoke_with_timeout(
        self,
        operation: Operation,
        context: OperationContext,
        timeout: float,
    ) -> OperationResult:
        """Invoke the handler with a timeout."""
        result_container: List[OperationResult] = []
        error_container: List[Exception] = []

        def _target():
            try:
                r = operation.handler(context)
                if not isinstance(r, OperationResult):
                    r = OperationResult(success=True, output=r)
                result_container.append(r)
            except Exception as e:
                error_container.append(e)

        thread = threading.Thread(target=_target, daemon=True)
        thread.start()
        thread.join(timeout=timeout)

        if thread.is_alive():
            return OperationResult(
                success=False,
                error=f"Operation '{operation.name}' timed out after {timeout}s",
            )

        if error_container:
            exc = error_container[0]
            if isinstance(exc, NonRetriableError):
                raise exc
            return OperationResult(
                success=False,
                error=f"{type(exc).__name__}: {str(exc)}",
            )

        if result_container:
            return result_container[0]

        return OperationResult(
            success=False,
            error="Handler completed without returning a result",
        )

    # ----- State Management Helpers -----

    def _mark_completed(self, op_name: str, result: OperationResult) -> None:
        with self._lock:
            if op_name not in self._completed:
                self._completed.append(op_name)
        self._logger.log(
            op_name,
            EventType.OPERATION_COMPLETE.value,
            {
                "cost": result.cost,
                "duration": result.duration,
                "attempts": result.attempt_count,
            },
            cost=result.cost,
        )
        self._statistics.record_cost(op_name, result.cost)

    def _mark_failed(self, op_name: str, result: OperationResult) -> None:
        with self._lock:
            if op_name not in self._failed:
                self._failed.append(op_name)
        sm = self._state_machines.get(op_name)
        if sm and sm.state != OperationState.FAILED:
            if sm.can_transition(OperationState.FAILED):
                sm.transition(OperationState.FAILED, result.error or "unknown")

    def _mark_skipped(self, op_name: str, reason: str) -> None:
        with self._lock:
            if (
                op_name not in self._skipped
                and op_name not in self._completed
                and op_name not in self._failed
            ):
                self._skipped.append(op_name)

        sm = self._state_machines.get(op_name)
        if sm and sm.state not in (OperationState.COMPLETED, OperationState.FAILED):
            if sm.can_transition(OperationState.SKIPPED):
                sm.transition(OperationState.SKIPPED, reason)

        self._logger.log(
            op_name,
            EventType.OPERATION_SKIPPED.value,
            {"reason": reason},
        )

        result = OperationResult(
            success=False,
            error=f"Skipped: {reason}",
        )
        with self._lock:
            if op_name not in self._operation_results:
                self._operation_results[op_name] = result

    def _handle_budget_exceeded(self, op_name: str) -> None:
        """Handle budget exceeded: log, abort, skip remaining."""
        self._aborted = True
        self._abort_reason = "budget_exceeded"
        self._logger.log(
            op_name,
            EventType.BUDGET_EXCEEDED.value,
            {
                "spent": self._budget.spent,
                "budget": self._config.max_budget,
            },
        )

    def _record_operation_cost(self, op_name: str, result: OperationResult) -> None:
        """Record cost in the budget tracker."""
        if result.cost > 0:
            self._budget.record_cost(op_name, result.cost)

    def _get_dependency_states(self) -> Dict[str, OperationState]:
        """Get current states for all operations."""
        states: Dict[str, OperationState] = {}
        for name, sm in self._state_machines.items():
            states[name] = sm.state
        return states

    def _build_context(
        self,
        operation_name: str,
        attempt: int = 1,
        max_attempts: Optional[int] = None,
    ) -> OperationContext:
        """Build an OperationContext for the given operation."""
        if max_attempts is None:
            op = self._registry.get(operation_name)
            max_attempts = (op.max_attempts if op and op.max_attempts else self._config.max_retries)

        return OperationContext(
            operation_name=operation_name,
            attempt=attempt,
            total_attempts=max_attempts,
            budget_remaining=self._budget.remaining,
            budget_utilization=self._budget.utilization,
            completed_operations=list(self._completed),
            failed_operations=list(self._failed),
            shared_data=self._shared_data,
            dry_run=self._config.dry_run,
        )

    def _build_result(self) -> WorkflowResult:
        """Build the final WorkflowResult."""
        total_duration = 0.0
        if self._start_time is not None:
            total_duration = time.monotonic() - self._start_time

        success = len(self._failed) == 0 and not self._aborted

        return WorkflowResult(
            success=success,
            total_cost=self._budget.spent,
            total_duration=total_duration,
            completed_operations=list(self._completed),
            failed_operations=list(self._failed),
            skipped_operations=list(self._skipped),
            operation_results=dict(self._operation_results),
            aborted=self._aborted,
            abort_reason=self._abort_reason,
        )

    # ----- Dry Run -----

    def dry_run(self) -> List[Dict[str, Any]]:
        """
        Simulate the workflow without executing handlers.

        Returns a list of dicts describing the planned execution order.
        """
        all_ops = self._registry.get_all()

        if not all_ops:
            return []

        # Validate first
        if not self._validator.validate(self._config, all_ops):
            return [{
                "operation": "validation",
                "status": "failed",
                "errors": self._validator.errors,
            }]

        graph = self._registry.build_dependency_graph()

        if self._config.parallel:
            groups = graph.get_parallel_groups()
            plan: List[Dict[str, Any]] = []
            cumulative_cost = 0.0

            for group_idx, group in enumerate(groups):
                for op_name in group:
                    op = all_ops[op_name]
                    cumulative_cost += op.estimated_cost
                    plan.append({
                        "operation": op_name,
                        "group": group_idx,
                        "parallel": len(group) > 1,
                        "dependencies": op.dependencies,
                        "estimated_cost": op.estimated_cost,
                        "cumulative_cost": cumulative_cost,
                        "max_attempts": op.max_attempts or self._config.max_retries,
                        "has_skip_condition": op.skip_condition is not None,
                        "has_recovery": op.recovery_handler is not None,
                        "tags": sorted(op.tags),
                    })

            return plan
        else:
            execution_order = graph.topological_sort()
            plan = []
            cumulative_cost = 0.0

            for idx, op_name in enumerate(execution_order):
                op = all_ops[op_name]
                cumulative_cost += op.estimated_cost
                plan.append({
                    "operation": op_name,
                    "order": idx,
                    "parallel": False,
                    "dependencies": op.dependencies,
                    "estimated_cost": op.estimated_cost,
                    "cumulative_cost": cumulative_cost,
                    "max_attempts": op.max_attempts or self._config.max_retries,
                    "has_skip_condition": op.skip_condition is not None,
                    "has_recovery": op.recovery_handler is not None,
                    "tags": sorted(op.tags),
                })

            return plan

    # ----- Log Access -----

    def get_log(self) -> List[LogEntry]:
        """Return all log entries."""
        return self._logger.get_entries()

    def get_log_for_operation(self, operation: str) -> List[LogEntry]:
        """Return log entries for a specific operation."""
        return self._logger.get_entries_for_operation(operation)

    def get_log_timeline(self) -> List[Dict[str, Any]]:
        """Return log entries as a timeline of dicts."""
        return self._logger.get_timeline()

    def export_log(self) -> str:
        """Export the full log as JSON."""
        return self._logger.export_json()

    # ----- Statistics Access -----

    def get_statistics(self) -> Dict[str, Any]:
        """Return execution statistics."""
        return self._statistics.get_summary()

    def get_budget_breakdown(self) -> Dict[str, float]:
        """Return per-operation cost breakdown."""
        return self._budget.get_cost_breakdown()

    # ----- Shared Data -----

    def set_shared_data(self, key: str, value: Any) -> None:
        """Set a value in shared data accessible to all operations."""
        self._shared_data[key] = value

    def get_shared_data(self, key: str, default: Any = None) -> Any:
        """Get a value from shared data."""
        return self._shared_data.get(key, default)

    # ----- State Inspection -----

    def get_operation_state(self, name: str) -> Optional[OperationState]:
        """Get the current state of an operation."""
        sm = self._state_machines.get(name)
        return sm.state if sm else None

    def get_all_states(self) -> Dict[str, OperationState]:
        """Get states for all operations."""
        return {name: sm.state for name, sm in self._state_machines.items()}

    def get_state_history(self, name: str) -> List[Tuple[OperationState, OperationState, str]]:
        """Get the state transition history for an operation."""
        sm = self._state_machines.get(name)
        return sm.history if sm else []

    # ----- Reset -----

    def reset(self) -> None:
        """Reset all runtime state, keeping registered operations."""
        self._budget.reset()
        self._cycle_detector.reset()
        self._logger.clear()
        self._operation_results.clear()
        self._shared_data.clear()
        self._execution_order.clear()
        self._completed.clear()
        self._failed.clear()
        self._skipped.clear()
        self._running = False
        self._aborted = False
        self._abort_reason = None
        self._start_time = None

        for sm in self._state_machines.values():
            sm.reset()

    # ----- Workflow Composition -----

    def clone_config(self) -> WorkflowConfig:
        """Return a copy of the current config."""
        return WorkflowConfig(**self._config.to_dict())

    def get_operation_names(self) -> List[str]:
        """Return names of all registered operations."""
        return self._registry.get_names()

    def get_operation(self, name: str) -> Optional[Operation]:
        """Get an operation by name."""
        return self._registry.get(name)

    def has_operation(self, name: str) -> bool:
        """Check if an operation is registered."""
        return self._registry.has(name)

    def get_execution_order(self) -> List[str]:
        """Return the execution order from the last run."""
        return list(self._execution_order)

    def validate(self) -> Tuple[bool, List[str], List[str]]:
        """
        Validate the workflow.

        Returns (is_valid, errors, warnings).
        """
        all_ops = self._registry.get_all()
        self._validator.validate(self._config, all_ops)
        return (
            self._validator.is_valid,
            self._validator.errors,
            self._validator.warnings,
        )

    def get_validation_report(self) -> str:
        """Return a formatted validation report."""
        self.validate()
        return self._validator.get_report()


# ===================================================================
# Workflow Builder (Fluent API)
# ===================================================================

class WorkflowBuilder:
    """
    Fluent builder for constructing workflows.

    Usage:
        result = (
            WorkflowBuilder()
            .with_budget(100.0)
            .with_retries(3)
            .add("build", build_handler)
            .add("test", test_handler, depends_on=["build"])
            .add("deploy", deploy_handler, depends_on=["test"])
            .run()
        )
    """

    def __init__(self):
        self._config_kwargs: Dict[str, Any] = {}
        self._operations: List[Dict[str, Any]] = []
        self._shared_data: Dict[str, Any] = {}

    def with_budget(self, budget: float) -> "WorkflowBuilder":
        self._config_kwargs["max_budget"] = budget
        return self

    def with_retries(self, retries: int) -> "WorkflowBuilder":
        self._config_kwargs["max_retries"] = retries
        return self

    def with_cycle_limit(self, limit: int) -> "WorkflowBuilder":
        self._config_kwargs["cycle_limit"] = limit
        return self

    def with_parallel(self, parallel: bool = True) -> "WorkflowBuilder":
        self._config_kwargs["parallel"] = parallel
        return self

    def with_dry_run(self, dry_run: bool = True) -> "WorkflowBuilder":
        self._config_kwargs["dry_run"] = dry_run
        return self

    def with_verbose(self, verbose: bool = True) -> "WorkflowBuilder":
        self._config_kwargs["verbose"] = verbose
        return self

    def with_config(self, **kwargs) -> "WorkflowBuilder":
        self._config_kwargs.update(kwargs)
        return self

    def with_shared_data(self, key: str, value: Any) -> "WorkflowBuilder":
        self._shared_data[key] = value
        return self

    def add(
        self,
        name: str,
        handler: Callable,
        depends_on: Optional[List[str]] = None,
        max_attempts: Optional[int] = None,
        estimated_cost: float = 0.0,
        timeout: Optional[float] = None,
        skip_condition: Optional[Callable] = None,
        recovery_handler: Optional[Callable] = None,
        tags: Optional[Set[str]] = None,
        retriable: bool = True,
    ) -> "WorkflowBuilder":
        self._operations.append({
            "name": name,
            "handler": handler,
            "dependencies": depends_on or [],
            "max_attempts": max_attempts,
            "estimated_cost": estimated_cost,
            "timeout": timeout,
            "skip_condition": skip_condition,
            "recovery_handler": recovery_handler,
            "tags": tags,
            "retriable": retriable,
        })
        return self

    def build(self) -> WorkflowEngine:
        """Build the WorkflowEngine without running it."""
        config = WorkflowConfig(**self._config_kwargs)
        engine = WorkflowEngine(config)

        for data in self._shared_data.items():
            engine.set_shared_data(data[0], data[1])

        for op in self._operations:
            engine.add_operation(**op)

        return engine

    def run(self) -> WorkflowResult:
        """Build and run the workflow."""
        engine = self.build()
        return engine.run()

    def dry_run(self) -> List[Dict[str, Any]]:
        """Build and dry-run the workflow."""
        engine = self.build()
        return engine.dry_run()


# ===================================================================
# Workflow Serializer
# ===================================================================

class WorkflowSerializer:
    """
    Serializes and deserializes workflow state for persistence
    or inspection.

    Note: handler functions cannot be serialized; this captures
    configuration, state, and logs only.
    """

    @staticmethod
    def serialize_result(result: WorkflowResult) -> str:
        """Serialize a WorkflowResult to JSON."""
        return json.dumps(result.to_dict(), default=str, indent=2)

    @staticmethod
    def serialize_log(entries: List[LogEntry]) -> str:
        """Serialize log entries to JSON."""
        return json.dumps(
            [e.to_dict() for e in entries], default=str, indent=2
        )

    @staticmethod
    def serialize_config(config: WorkflowConfig) -> str:
        """Serialize a WorkflowConfig to JSON."""
        return json.dumps(config.to_dict(), indent=2)

    @staticmethod
    def deserialize_config(json_str: str) -> WorkflowConfig:
        """Deserialize a WorkflowConfig from JSON."""
        data = json.loads(json_str)
        return WorkflowConfig(**data)

    @staticmethod
    def serialize_plan(plan: List[Dict[str, Any]]) -> str:
        """Serialize a dry-run plan to JSON."""
        return json.dumps(plan, default=str, indent=2)

    @staticmethod
    def serialize_statistics(stats: Dict[str, Any]) -> str:
        """Serialize statistics to JSON."""
        return json.dumps(stats, default=str, indent=2)


# ===================================================================
# Workflow Templates
# ===================================================================

class WorkflowTemplates:
    """
    Provides factory methods for common workflow patterns.

    These are convenience methods for constructing typical workflows
    without manually wiring everything up.
    """

    @staticmethod
    def linear_pipeline(
        operations: List[Tuple[str, Callable]],
        budget: float = 1000.0,
        retries: int = 3,
    ) -> WorkflowEngine:
        """
        Create a linear pipeline where each operation depends on the previous.

        Parameters
        ----------
        operations : list of (name, handler) tuples
        budget : float
        retries : int
        """
        config = WorkflowConfig(max_budget=budget, max_retries=retries)
        engine = WorkflowEngine(config)

        prev_name: Optional[str] = None
        for name, handler in operations:
            deps = [prev_name] if prev_name else []
            engine.add_operation(name, handler, dependencies=deps)
            prev_name = name

        return engine

    @staticmethod
    def fan_out_fan_in(
        setup: Tuple[str, Callable],
        parallel_ops: List[Tuple[str, Callable]],
        aggregate: Tuple[str, Callable],
        budget: float = 1000.0,
    ) -> WorkflowEngine:
        """
        Create a fan-out/fan-in workflow:
            setup -> [parallel_ops] -> aggregate

        Parameters
        ----------
        setup : (name, handler) for the initial operation
        parallel_ops : list of (name, handler) that run after setup
        aggregate : (name, handler) that runs after all parallel_ops complete
        budget : float
        """
        config = WorkflowConfig(
            max_budget=budget,
            parallel=True,
        )
        engine = WorkflowEngine(config)

        engine.add_operation(setup[0], setup[1])

        for name, handler in parallel_ops:
            engine.add_operation(name, handler, dependencies=[setup[0]])

        aggregate_deps = [name for name, _ in parallel_ops]
        engine.add_operation(
            aggregate[0], aggregate[1], dependencies=aggregate_deps
        )

        return engine

    @staticmethod
    def diamond(
        start: Tuple[str, Callable],
        left: Tuple[str, Callable],
        right: Tuple[str, Callable],
        end: Tuple[str, Callable],
        budget: float = 1000.0,
    ) -> WorkflowEngine:
        """
        Create a diamond-shaped workflow:
            start -> left  \\
            start -> right -> end

        Parameters
        ----------
        start, left, right, end : (name, handler) tuples
        budget : float
        """
        config = WorkflowConfig(max_budget=budget, parallel=True)
        engine = WorkflowEngine(config)

        engine.add_operation(start[0], start[1])
        engine.add_operation(left[0], left[1], dependencies=[start[0]])
        engine.add_operation(right[0], right[1], dependencies=[start[0]])
        engine.add_operation(
            end[0], end[1], dependencies=[left[0], right[0]]
        )

        return engine

    @staticmethod
    def retry_heavy(
        operations: List[Tuple[str, Callable]],
        max_retries: int = 5,
        budget: float = 1000.0,
    ) -> WorkflowEngine:
        """Create a workflow with aggressive retry settings."""
        config = WorkflowConfig(
            max_budget=budget,
            max_retries=max_retries,
            backoff_base=0.01,
            backoff_max=1.0,
            jitter_factor=0.05,
        )
        engine = WorkflowEngine(config)

        for name, handler in operations:
            engine.add_operation(name, handler, max_attempts=max_retries)

        return engine


# ===================================================================
# Workflow Hooks
# ===================================================================

class WorkflowHooks:
    """
    Manages pre- and post-execution hooks for workflow operations.

    Hooks can observe or modify behavior at key points in the
    workflow lifecycle.
    """

    def __init__(self):
        self._pre_operation: List[Callable] = []
        self._post_operation: List[Callable] = []
        self._pre_workflow: List[Callable] = []
        self._post_workflow: List[Callable] = []
        self._on_error: List[Callable] = []
        self._on_retry: List[Callable] = []
        self._on_skip: List[Callable] = []

    def add_pre_operation(self, hook: Callable) -> None:
        """Add a hook called before each operation."""
        self._pre_operation.append(hook)

    def add_post_operation(self, hook: Callable) -> None:
        """Add a hook called after each operation."""
        self._post_operation.append(hook)

    def add_pre_workflow(self, hook: Callable) -> None:
        self._pre_workflow.append(hook)

    def add_post_workflow(self, hook: Callable) -> None:
        self._post_workflow.append(hook)

    def add_on_error(self, hook: Callable) -> None:
        self._on_error.append(hook)

    def add_on_retry(self, hook: Callable) -> None:
        self._on_retry.append(hook)

    def add_on_skip(self, hook: Callable) -> None:
        self._on_skip.append(hook)

    def fire_pre_operation(self, operation_name: str, context: OperationContext) -> None:
        for hook in self._pre_operation:
            try:
                hook(operation_name, context)
            except Exception:
                _logger.warning("Pre-operation hook failed for '%s'", operation_name)

    def fire_post_operation(
        self, operation_name: str, result: OperationResult
    ) -> None:
        for hook in self._post_operation:
            try:
                hook(operation_name, result)
            except Exception:
                _logger.warning("Post-operation hook failed for '%s'", operation_name)

    def fire_pre_workflow(self, config: WorkflowConfig) -> None:
        for hook in self._pre_workflow:
            try:
                hook(config)
            except Exception:
                _logger.warning("Pre-workflow hook failed")

    def fire_post_workflow(self, result: WorkflowResult) -> None:
        for hook in self._post_workflow:
            try:
                hook(result)
            except Exception:
                _logger.warning("Post-workflow hook failed")

    def fire_on_error(self, operation_name: str, error: str) -> None:
        for hook in self._on_error:
            try:
                hook(operation_name, error)
            except Exception:
                _logger.warning("On-error hook failed for '%s'", operation_name)

    def fire_on_retry(self, operation_name: str, attempt: int) -> None:
        for hook in self._on_retry:
            try:
                hook(operation_name, attempt)
            except Exception:
                _logger.warning("On-retry hook failed for '%s'", operation_name)

    def fire_on_skip(self, operation_name: str, reason: str) -> None:
        for hook in self._on_skip:
            try:
                hook(operation_name, reason)
            except Exception:
                _logger.warning("On-skip hook failed for '%s'", operation_name)


# ===================================================================
# Workflow Report Generator
# ===================================================================

class WorkflowReportGenerator:
    """
    Generates human-readable reports from workflow results and logs.
    """

    def __init__(self, result: WorkflowResult, log_entries: List[LogEntry]):
        self._result = result
        self._log_entries = log_entries

    def generate_summary(self) -> str:
        """Generate a concise summary report."""
        lines = [
            "=" * 60,
            "WORKFLOW EXECUTION REPORT",
            "=" * 60,
            "",
            f"Status     : {'SUCCESS' if self._result.success else 'FAILED'}",
            f"Total Cost : {self._result.total_cost:.2f}",
            f"Duration   : {self._result.total_duration:.4f}s",
            "",
            f"Completed  : {len(self._result.completed_operations)}",
        ]

        for op in self._result.completed_operations:
            r = self._result.operation_results.get(op)
            if r:
                lines.append(
                    f"  - {op} (cost={r.cost:.2f}, duration={r.duration:.4f}s, "
                    f"attempts={r.attempt_count})"
                )
            else:
                lines.append(f"  - {op}")

        lines.append(f"\nFailed     : {len(self._result.failed_operations)}")
        for op in self._result.failed_operations:
            r = self._result.operation_results.get(op)
            if r:
                lines.append(f"  - {op}: {r.error}")
            else:
                lines.append(f"  - {op}")

        lines.append(f"\nSkipped    : {len(self._result.skipped_operations)}")
        for op in self._result.skipped_operations:
            r = self._result.operation_results.get(op)
            if r:
                lines.append(f"  - {op}: {r.error}")
            else:
                lines.append(f"  - {op}")

        if self._result.aborted:
            lines.append(f"\nABORTED: {self._result.abort_reason}")

        lines.append("")
        lines.append("=" * 60)
        return "\n".join(lines)

    def generate_timeline(self) -> str:
        """Generate a chronological timeline of events."""
        lines = [
            "TIMELINE",
            "-" * 60,
        ]

        sorted_entries = sorted(self._log_entries, key=lambda e: e.timestamp)
        for entry in sorted_entries:
            cost_str = f" [cost={entry.cost:.2f}]" if entry.cost > 0 else ""
            lines.append(
                f"  {entry.timestamp} | {entry.operation:20s} | "
                f"{entry.event_type}{cost_str}"
            )

        return "\n".join(lines)

    def generate_cost_report(self) -> str:
        """Generate a breakdown of costs per operation."""
        lines = [
            "COST BREAKDOWN",
            "-" * 40,
        ]

        cost_by_op: Dict[str, float] = defaultdict(float)
        for entry in self._log_entries:
            if entry.cost > 0:
                cost_by_op[entry.operation] += entry.cost

        if not cost_by_op:
            lines.append("  No costs recorded.")
        else:
            for op, cost in sorted(
                cost_by_op.items(), key=lambda x: -x[1]
            ):
                pct = (
                    (cost / self._result.total_cost * 100)
                    if self._result.total_cost > 0
                    else 0
                )
                lines.append(f"  {op:30s} {cost:8.2f}  ({pct:5.1f}%)")

            lines.append(f"  {'TOTAL':30s} {self._result.total_cost:8.2f}")

        return "\n".join(lines)

    def generate_full_report(self) -> str:
        """Generate a comprehensive report."""
        sections = [
            self.generate_summary(),
            "",
            self.generate_timeline(),
            "",
            self.generate_cost_report(),
        ]
        return "\n".join(sections)


# ===================================================================
# Utility Functions
# ===================================================================

def create_simple_handler(
    output: Any = "ok",
    cost: float = 1.0,
    duration: float = 0.0,
    success: bool = True,
    error: Optional[str] = None,
) -> Callable:
    """
    Create a simple handler function for testing or prototyping.

    Returns a callable that ignores the context argument and returns
    a fixed OperationResult.
    """
    def handler(context):
        if duration > 0:
            time.sleep(duration)
        return OperationResult(
            success=success,
            cost=cost,
            duration=duration,
            output=output,
            error=error,
        )
    return handler


def create_conditional_handler(
    success_output: Any = "ok",
    failure_output: Any = "fail",
    success_cost: float = 1.0,
    failure_cost: float = 0.5,
    fail_on_attempts: Optional[Set[int]] = None,
) -> Callable:
    """
    Create a handler that fails on specific attempt numbers.

    Useful for testing retry logic.
    """
    def handler(context):
        attempt = getattr(context, "attempt", 1)
        if fail_on_attempts and attempt in fail_on_attempts:
            return OperationResult(
                success=False,
                cost=failure_cost,
                error=f"Intentional failure on attempt {attempt}",
                output=failure_output,
            )
        return OperationResult(
            success=True,
            cost=success_cost,
            output=success_output,
        )
    return handler


def create_flaky_handler(
    failure_rate: float = 0.5,
    cost: float = 1.0,
    seed: Optional[int] = None,
) -> Callable:
    """
    Create a handler that fails randomly based on failure_rate.

    Parameters
    ----------
    failure_rate : float
        Probability of failure (0.0 to 1.0).
    cost : float
        Cost per execution.
    seed : int, optional
        Random seed for reproducibility.
    """
    rng = random.Random(seed)

    def handler(context):
        if rng.random() < failure_rate:
            return OperationResult(
                success=False,
                cost=cost * 0.5,
                error="Random failure",
            )
        return OperationResult(
            success=True,
            cost=cost,
            output="ok",
        )
    return handler


def create_expensive_handler(
    base_cost: float = 10.0,
    cost_multiplier: float = 1.5,
) -> Callable:
    """
    Create a handler whose cost increases with each attempt.
    """
    def handler(context):
        attempt = getattr(context, "attempt", 1)
        cost = base_cost * (cost_multiplier ** (attempt - 1))
        return OperationResult(
            success=True,
            cost=cost,
            output=f"completed at cost {cost:.2f}",
        )
    return handler


def create_slow_handler(
    duration: float = 1.0,
    cost: float = 1.0,
) -> Callable:
    """Create a handler that takes a specified duration."""
    def handler(context):
        time.sleep(duration)
        return OperationResult(
            success=True,
            cost=cost,
            duration=duration,
            output="slow but done",
        )
    return handler


def create_error_handler(
    error_message: str = "Something went wrong",
    error_type: str = "RuntimeError",
    retriable: bool = True,
) -> Callable:
    """Create a handler that always raises an exception."""
    def handler(context):
        if not retriable:
            raise NonRetriableError(error_message)
        raise RuntimeError(error_message)
    return handler


def create_stateful_handler(initial_state: Any = None) -> Tuple[Callable, Dict[str, Any]]:
    """
    Create a handler that maintains internal state across calls.

    Returns (handler, state_dict) so the caller can inspect state.
    """
    state = {"call_count": 0, "data": initial_state, "history": []}

    def handler(context):
        state["call_count"] += 1
        state["history"].append({
            "operation": context.operation_name,
            "attempt": context.attempt,
            "budget_remaining": context.budget_remaining,
        })
        return OperationResult(
            success=True,
            cost=1.0,
            output=f"call #{state['call_count']}",
        )

    return handler, state


def create_recovery_handler(
    success: bool = True,
    cost: float = 0.5,
) -> Callable:
    """
    Create a recovery handler for use with operations.

    Parameters
    ----------
    success : bool
        Whether recovery succeeds.
    cost : float
        Cost of recovery.
    """
    def handler(context, error_str):
        return OperationResult(
            success=success,
            cost=cost,
            output=f"recovered from: {error_str}" if success else None,
            error=None if success else f"Recovery failed for: {error_str}",
        )
    return handler


# ===================================================================
# Workflow Analyzer
# ===================================================================

class WorkflowAnalyzer:
    """
    Analyzes workflow structure and provides insights.

    Useful for understanding complex workflows before execution.
    """

    def __init__(self, engine: WorkflowEngine):
        self._engine = engine

    def get_critical_path(self) -> List[str]:
        """
        Identify the critical path (longest chain of dependencies).

        Returns a list of operation names from start to end.
        """
        all_ops = self._engine.operations
        if not all_ops:
            return []

        graph = OperationRegistry()
        for name, op in all_ops.items():
            graph.register(op)

        dep_graph = graph.build_dependency_graph()

        try:
            topo_order = dep_graph.topological_sort()
        except WorkflowError:
            return []

        # Build longest-path using dynamic programming
        distances: Dict[str, int] = {name: 0 for name in topo_order}
        predecessors: Dict[str, Optional[str]] = {name: None for name in topo_order}

        for node in topo_order:
            op = all_ops.get(node)
            if op:
                for dep in op.dependencies:
                    if distances.get(dep, 0) + 1 > distances[node]:
                        distances[node] = distances[dep] + 1
                        predecessors[node] = dep

        # Find the node with the longest distance
        if not distances:
            return []

        end_node = max(distances, key=distances.get)

        # Trace back the critical path
        path: List[str] = []
        current: Optional[str] = end_node
        while current is not None:
            path.append(current)
            current = predecessors.get(current)
        path.reverse()

        return path

    def get_parallelism_factor(self) -> float:
        """
        Calculate the theoretical parallelism factor.

        Returns the ratio of total operations to critical path length.
        A higher factor means more parallelism is possible.
        """
        critical_path = self.get_critical_path()
        total_ops = self._engine.operation_count

        if not critical_path or total_ops == 0:
            return 1.0

        return total_ops / len(critical_path)

    def get_bottlenecks(self) -> List[str]:
        """
        Identify bottleneck operations (those with the most dependents).
        """
        all_ops = self._engine.operations
        if not all_ops:
            return []

        dependent_count: Dict[str, int] = defaultdict(int)
        for name, op in all_ops.items():
            for dep in op.dependencies:
                dependent_count[dep] += 1

        if not dependent_count:
            return []

        max_deps = max(dependent_count.values())
        return [
            name for name, count in dependent_count.items()
            if count == max_deps
        ]

    def get_leaf_operations(self) -> List[str]:
        """Return operations with no dependents (end of pipeline)."""
        all_ops = self._engine.operations
        all_deps: Set[str] = set()
        for op in all_ops.values():
            all_deps.update(op.dependencies)

        return [name for name in all_ops if name not in all_deps]

    def get_root_operations(self) -> List[str]:
        """Return operations with no dependencies (start of pipeline)."""
        all_ops = self._engine.operations
        return [
            name for name, op in all_ops.items()
            if not op.dependencies
        ]

    def estimate_total_cost(self) -> float:
        """Sum up estimated costs for all operations."""
        return sum(
            op.estimated_cost for op in self._engine.operations.values()
        )

    def estimate_worst_case_cost(self) -> float:
        """
        Estimate worst-case cost assuming all operations use max retries.
        """
        total = 0.0
        config = self._engine.config
        for op in self._engine.operations.values():
            max_attempts = op.max_attempts or config.max_retries
            total += op.estimated_cost * max_attempts
        return total

    def get_dependency_depth(self) -> Dict[str, int]:
        """Return the depth (distance from root) for each operation."""
        all_ops = self._engine.operations
        depths: Dict[str, int] = {}

        def _compute_depth(name: str) -> int:
            if name in depths:
                return depths[name]
            op = all_ops.get(name)
            if not op or not op.dependencies:
                depths[name] = 0
                return 0
            max_dep_depth = max(
                _compute_depth(dep) for dep in op.dependencies
                if dep in all_ops
            )
            depths[name] = max_dep_depth + 1
            return depths[name]

        for name in all_ops:
            _compute_depth(name)

        return depths

    def get_structure_summary(self) -> Dict[str, Any]:
        """Return a summary of the workflow structure."""
        return {
            "total_operations": self._engine.operation_count,
            "root_operations": self.get_root_operations(),
            "leaf_operations": self.get_leaf_operations(),
            "critical_path": self.get_critical_path(),
            "parallelism_factor": self.get_parallelism_factor(),
            "bottlenecks": self.get_bottlenecks(),
            "estimated_cost": self.estimate_total_cost(),
            "worst_case_cost": self.estimate_worst_case_cost(),
            "dependency_depths": self.get_dependency_depth(),
        }


# ===================================================================
# Workflow Middleware
# ===================================================================

class WorkflowMiddleware:
    """
    Base class for workflow middleware that can intercept and modify
    operation execution.

    Subclass and override methods to add cross-cutting concerns
    like logging, metrics, or rate limiting.
    """

    def before_operation(
        self, operation: Operation, context: OperationContext
    ) -> Optional[OperationContext]:
        """
        Called before an operation executes.

        Return a modified context or None to use the original.
        """
        return None

    def after_operation(
        self, operation: Operation, result: OperationResult
    ) -> Optional[OperationResult]:
        """
        Called after an operation completes.

        Return a modified result or None to use the original.
        """
        return None

    def on_error(
        self, operation: Operation, error: Exception
    ) -> Optional[OperationResult]:
        """
        Called when an operation raises an exception.

        Return an OperationResult to suppress the error, or None to propagate.
        """
        return None


class TimingMiddleware(WorkflowMiddleware):
    """Middleware that tracks detailed timing for each operation."""

    def __init__(self):
        self._timings: Dict[str, List[float]] = defaultdict(list)
        self._start_times: Dict[str, float] = {}

    def before_operation(
        self, operation: Operation, context: OperationContext
    ) -> Optional[OperationContext]:
        self._start_times[operation.name] = time.monotonic()
        return None

    def after_operation(
        self, operation: Operation, result: OperationResult
    ) -> Optional[OperationResult]:
        start = self._start_times.pop(operation.name, None)
        if start is not None:
            elapsed = time.monotonic() - start
            self._timings[operation.name].append(elapsed)
        return None

    def get_timings(self) -> Dict[str, List[float]]:
        return dict(self._timings)

    def get_average_timings(self) -> Dict[str, float]:
        return {
            op: sum(times) / len(times)
            for op, times in self._timings.items()
            if times
        }


class CostTrackingMiddleware(WorkflowMiddleware):
    """Middleware that provides detailed cost tracking per operation."""

    def __init__(self):
        self._costs: Dict[str, List[float]] = defaultdict(list)

    def after_operation(
        self, operation: Operation, result: OperationResult
    ) -> Optional[OperationResult]:
        self._costs[operation.name].append(result.cost)
        return None

    def get_costs(self) -> Dict[str, List[float]]:
        return dict(self._costs)

    def get_total_cost(self) -> float:
        return sum(c for costs in self._costs.values() for c in costs)


class RateLimitMiddleware(WorkflowMiddleware):
    """Middleware that enforces a minimum delay between operations."""

    def __init__(self, min_delay: float = 0.1):
        self._min_delay = min_delay
        self._last_execution: float = 0

    def before_operation(
        self, operation: Operation, context: OperationContext
    ) -> Optional[OperationContext]:
        now = time.monotonic()
        elapsed = now - self._last_execution
        if elapsed < self._min_delay:
            time.sleep(self._min_delay - elapsed)
        self._last_execution = time.monotonic()
        return None


# ===================================================================
# Workflow Checkpointer
# ===================================================================

class WorkflowCheckpointer:
    """
    Manages checkpoints for long-running workflows.

    Allows saving and restoring workflow state at points between
    operations, enabling resumability.
    """

    def __init__(self):
        self._checkpoints: Dict[str, Dict[str, Any]] = {}
        self._lock = threading.Lock()

    def save_checkpoint(
        self,
        name: str,
        completed: List[str],
        failed: List[str],
        skipped: List[str],
        total_cost: float,
        shared_data: Dict[str, Any],
    ) -> None:
        """Save a checkpoint with the current workflow state."""
        with self._lock:
            self._checkpoints[name] = {
                "completed": list(completed),
                "failed": list(failed),
                "skipped": list(skipped),
                "total_cost": total_cost,
                "shared_data": copy.deepcopy(shared_data),
                "timestamp": datetime.now(timezone.utc).isoformat(),
            }

    def load_checkpoint(self, name: str) -> Optional[Dict[str, Any]]:
        """Load a previously saved checkpoint."""
        with self._lock:
            cp = self._checkpoints.get(name)
            return copy.deepcopy(cp) if cp else None

    def list_checkpoints(self) -> List[str]:
        """List all checkpoint names."""
        with self._lock:
            return list(self._checkpoints.keys())

    def delete_checkpoint(self, name: str) -> bool:
        """Delete a checkpoint. Returns True if it existed."""
        with self._lock:
            return self._checkpoints.pop(name, None) is not None

    def clear(self) -> None:
        """Remove all checkpoints."""
        with self._lock:
            self._checkpoints.clear()

    def get_latest(self) -> Optional[Dict[str, Any]]:
        """Get the most recent checkpoint."""
        with self._lock:
            if not self._checkpoints:
                return None
            latest_name = max(
                self._checkpoints,
                key=lambda k: self._checkpoints[k]["timestamp"],
            )
            return copy.deepcopy(self._checkpoints[latest_name])


# ===================================================================
# Workflow Event Bus
# ===================================================================

class WorkflowEventBus:
    """
    Simple pub-sub event bus for workflow events.

    Allows external systems to subscribe to workflow events
    without tight coupling.
    """

    def __init__(self):
        self._subscribers: Dict[str, List[Callable]] = defaultdict(list)
        self._lock = threading.Lock()

    def subscribe(self, event_type: str, callback: Callable) -> None:
        """Subscribe to a specific event type."""
        with self._lock:
            self._subscribers[event_type].append(callback)

    def unsubscribe(self, event_type: str, callback: Callable) -> None:
        """Unsubscribe from a specific event type."""
        with self._lock:
            subs = self._subscribers.get(event_type, [])
            if callback in subs:
                subs.remove(callback)

    def publish(self, event_type: str, data: Dict[str, Any]) -> None:
        """Publish an event to all subscribers."""
        with self._lock:
            callbacks = list(self._subscribers.get(event_type, []))

        for callback in callbacks:
            try:
                callback(event_type, data)
            except Exception:
                _logger.warning("Event bus subscriber failed for '%s'", event_type)

    def clear(self) -> None:
        with self._lock:
            self._subscribers.clear()

    def subscriber_count(self, event_type: str) -> int:
        with self._lock:
            return len(self._subscribers.get(event_type, []))


# ===================================================================
# Workflow Metric Collector
# ===================================================================

class WorkflowMetricCollector:
    """
    Collects numerical metrics during workflow execution.

    Supports counters, gauges, and histograms.
    """

    def __init__(self):
        self._counters: Dict[str, int] = defaultdict(int)
        self._gauges: Dict[str, float] = {}
        self._histograms: Dict[str, List[float]] = defaultdict(list)
        self._lock = threading.Lock()

    def increment(self, name: str, amount: int = 1) -> None:
        with self._lock:
            self._counters[name] += amount

    def set_gauge(self, name: str, value: float) -> None:
        with self._lock:
            self._gauges[name] = value

    def record_histogram(self, name: str, value: float) -> None:
        with self._lock:
            self._histograms[name].append(value)

    def get_counter(self, name: str) -> int:
        with self._lock:
            return self._counters.get(name, 0)

    def get_gauge(self, name: str) -> Optional[float]:
        with self._lock:
            return self._gauges.get(name)

    def get_histogram_stats(self, name: str) -> Dict[str, float]:
        with self._lock:
            values = self._histograms.get(name, [])

        if not values:
            return {"count": 0, "min": 0, "max": 0, "mean": 0, "sum": 0}

        sorted_vals = sorted(values)
        return {
            "count": len(sorted_vals),
            "min": sorted_vals[0],
            "max": sorted_vals[-1],
            "mean": sum(sorted_vals) / len(sorted_vals),
            "sum": sum(sorted_vals),
            "p50": sorted_vals[len(sorted_vals) // 2],
            "p95": sorted_vals[int(len(sorted_vals) * 0.95)],
            "p99": sorted_vals[int(len(sorted_vals) * 0.99)],
        }

    def get_all_metrics(self) -> Dict[str, Any]:
        with self._lock:
            return {
                "counters": dict(self._counters),
                "gauges": dict(self._gauges),
                "histograms": {
                    name: self.get_histogram_stats(name)
                    for name in self._histograms
                },
            }

    def reset(self) -> None:
        with self._lock:
            self._counters.clear()
            self._gauges.clear()
            self._histograms.clear()


# ===================================================================
# Workflow Condition Evaluator
# ===================================================================

class WorkflowConditionEvaluator:
    """
    Evaluates complex conditions for workflow branching.

    Conditions can reference operation results, shared data,
    and budget state.
    """

    def __init__(self, engine: WorkflowEngine):
        self._engine = engine

    def operation_succeeded(self, name: str) -> bool:
        """Check if an operation completed successfully."""
        state = self._engine.get_operation_state(name)
        return state == OperationState.COMPLETED

    def operation_failed(self, name: str) -> bool:
        state = self._engine.get_operation_state(name)
        return state == OperationState.FAILED

    def operation_skipped(self, name: str) -> bool:
        state = self._engine.get_operation_state(name)
        return state == OperationState.SKIPPED

    def all_succeeded(self, names: List[str]) -> bool:
        return all(self.operation_succeeded(n) for n in names)

    def any_failed(self, names: List[str]) -> bool:
        return any(self.operation_failed(n) for n in names)

    def budget_below(self, threshold: float) -> bool:
        return self._engine.budget_remaining < threshold

    def budget_above(self, threshold: float) -> bool:
        return self._engine.budget_remaining > threshold

    def shared_data_equals(self, key: str, value: Any) -> bool:
        return self._engine.get_shared_data(key) == value

    def shared_data_exists(self, key: str) -> bool:
        return self._engine.get_shared_data(key) is not None

    def evaluate(self, condition: Dict[str, Any]) -> bool:
        """
        Evaluate a condition dict.

        Supported condition types:
            {"type": "operation_succeeded", "name": "build"}
            {"type": "budget_below", "threshold": 10.0}
            {"type": "all_succeeded", "names": ["build", "test"]}
            {"type": "shared_data_equals", "key": "env", "value": "prod"}
            {"type": "and", "conditions": [...]}
            {"type": "or", "conditions": [...]}
            {"type": "not", "condition": {...}}
        """
        ctype = condition.get("type", "")

        if ctype == "operation_succeeded":
            return self.operation_succeeded(condition["name"])
        elif ctype == "operation_failed":
            return self.operation_failed(condition["name"])
        elif ctype == "operation_skipped":
            return self.operation_skipped(condition["name"])
        elif ctype == "all_succeeded":
            return self.all_succeeded(condition["names"])
        elif ctype == "any_failed":
            return self.any_failed(condition["names"])
        elif ctype == "budget_below":
            return self.budget_below(condition["threshold"])
        elif ctype == "budget_above":
            return self.budget_above(condition["threshold"])
        elif ctype == "shared_data_equals":
            return self.shared_data_equals(condition["key"], condition["value"])
        elif ctype == "shared_data_exists":
            return self.shared_data_exists(condition["key"])
        elif ctype == "and":
            return all(self.evaluate(c) for c in condition["conditions"])
        elif ctype == "or":
            return any(self.evaluate(c) for c in condition["conditions"])
        elif ctype == "not":
            return not self.evaluate(condition["condition"])
        else:
            raise ValueError(f"Unknown condition type: {ctype}")


# ===================================================================
# Exports
# ===================================================================

__all__ = [
    # Enums
    "OperationState",
    "EventType",
    # Exceptions
    "WorkflowError",
    "InvalidTransitionError",
    "CycleDetectedError",
    "BudgetExceededError",
    "DependencyError",
    "NonRetriableError",
    # Data classes
    "OperationResult",
    "LogEntry",
    "WorkflowConfig",
    "Operation",
    "WorkflowResult",
    # Core classes
    "OperationStateMachine",
    "DependencyGraph",
    "BackoffCalculator",
    "CycleDetector",
    "BudgetTracker",
    "EventLogger",
    "OperationContext",
    "WorkflowValidator",
    "WorkflowStatistics",
    "OperationRegistry",
    "ParallelExecutor",
    "RecoveryManager",
    "SkipEvaluator",
    "WorkflowEngine",
    "WorkflowBuilder",
    "WorkflowSerializer",
    "WorkflowTemplates",
    "WorkflowHooks",
    "WorkflowReportGenerator",
    "WorkflowAnalyzer",
    "WorkflowMiddleware",
    "TimingMiddleware",
    "CostTrackingMiddleware",
    "RateLimitMiddleware",
    "WorkflowCheckpointer",
    "WorkflowEventBus",
    "WorkflowMetricCollector",
    "WorkflowConditionEvaluator",
    # Utility functions
    "create_simple_handler",
    "create_conditional_handler",
    "create_flaky_handler",
    "create_expensive_handler",
    "create_slow_handler",
    "create_error_handler",
    "create_stateful_handler",
    "create_recovery_handler",
]
