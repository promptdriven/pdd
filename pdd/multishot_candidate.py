"""Multi-shot candidate generation and selection artifacts.

Implements the public artifact schemas for Issue #1475:
  - selection_policy.json
  - candidate_records.jsonl
  - pass_at_k.json
  - selection_regret.json

Start here when integrating with the research/ harness; artifact schemas are
kept independent so they can later feed the router described in #1431.
"""
from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

SCHEMA_VERSION: int = 1

# ---------------------------------------------------------------------------
# Exceptions
# ---------------------------------------------------------------------------


class LeakageError(ValueError):
    """Raised when a selector input is derived from hidden results."""


class FrozenStateError(RuntimeError):
    """Raised when hidden labels are accessed before selection is frozen."""


# ---------------------------------------------------------------------------
# Selection policy model
# ---------------------------------------------------------------------------


@dataclass
class SelectionPolicy:
    """Immutable policy governing candidate selection.

    Must be frozen before any candidate is generated; ``frozen_before_generation``
    is enforced in ``__post_init__`` so it cannot be constructed in an invalid state.
    """

    schema_version: int
    frozen_before_generation: bool
    uses_hidden_results: bool
    trained_on_confirmation_hidden: bool
    tuned_on_confirmation_hidden: bool
    training_sources: list[dict[str, Any]]
    tiebreak_order: list[str]

    def __post_init__(self) -> None:
        if not self.frozen_before_generation:
            raise ValueError(
                "Selection policy requires frozen_before_generation=True; "
                "policy must be frozen before any candidate is generated."
            )

    def to_dict(self) -> dict[str, Any]:
        """Return a JSON-serializable dict."""
        return asdict(self)

    def to_json(self, *, indent: int = 2) -> str:
        """Serialize to a JSON string."""
        return json.dumps(self.to_dict(), indent=indent)


def default_policy() -> SelectionPolicy:
    """Return the canonical default selection policy (no hidden signals)."""
    return SelectionPolicy(
        schema_version=SCHEMA_VERSION,
        frozen_before_generation=True,
        uses_hidden_results=False,
        trained_on_confirmation_hidden=False,
        tuned_on_confirmation_hidden=False,
        training_sources=[
            {
                "name": "public-benchmark-v1",
                "leakage_from_hidden_labels": False,
                "leakage_from_hidden_stdout": False,
                "leakage_from_hidden_test_names": False,
            }
        ],
        tiebreak_order=["lint_pass", "parse_ok", "test_pass", "candidate_index"],
    )


# ---------------------------------------------------------------------------
# Candidate record
# ---------------------------------------------------------------------------

_REQUIRED_FIELDS: frozenset[str] = frozenset(
    {
        "task_id",
        "arm_id",
        "candidate_index",
        "model",
        "harness",
        "public_signals",
        "selected",
    }
)


@dataclass
class CandidateRecord:
    """One row in ``candidate_records.jsonl``."""

    task_id: str
    arm_id: str
    candidate_index: int
    model: str
    harness: str
    public_signals: dict[str, Any]
    selected: bool
    hidden_status: str | None = None  # None until selection is frozen

    def __post_init__(self) -> None:
        if not isinstance(self.candidate_index, int):
            raise TypeError(
                f"candidate_index must be int, got {type(self.candidate_index).__name__}"
            )

    def to_dict(self, *, include_hidden: bool = False) -> dict[str, Any]:
        """Return a JSON-serializable dict.

        ``hidden_status`` is omitted unless *include_hidden* is True and the
        field is not None, matching the freeze lifecycle requirement.
        """
        d = asdict(self)
        if not include_hidden or d["hidden_status"] is None:
            del d["hidden_status"]
        return d


def validate_candidate_record(data: dict[str, Any]) -> None:
    """Raise ValueError / TypeError for missing or badly-typed fields."""
    missing = sorted(_REQUIRED_FIELDS - data.keys())
    if missing:
        raise ValueError(f"Missing required fields: {missing}")
    if not isinstance(data.get("candidate_index"), int):
        raise TypeError(
            f"candidate_index must be int, got "
            f"{type(data.get('candidate_index')).__name__}"
        )


def check_duplicate_candidate_indices(records: list[CandidateRecord]) -> None:
    """Raise ValueError if any (task_id, candidate_index) pair is duplicated."""
    seen: set[tuple[str, int]] = set()
    for rec in records:
        key = (rec.task_id, rec.candidate_index)
        if key in seen:
            raise ValueError(f"Duplicate (task_id, candidate_index): {key}")
        seen.add(key)


# ---------------------------------------------------------------------------
# Hidden-label lifecycle guard
# ---------------------------------------------------------------------------


class CandidateRun:
    """Manages the lifecycle of a multi-shot run: generation → freeze → scoring.

    Hidden labels may only be unsealed after ``freeze()`` is called, ensuring
    that selection was completed before any hidden signal could influence it.
    """

    def __init__(self, policy: SelectionPolicy) -> None:
        self._policy = policy
        self._records: list[CandidateRecord] = []
        self._frozen: bool = False

    def add_record(self, record: CandidateRecord) -> None:
        self._records.append(record)

    def freeze(self) -> None:
        """Freeze selection. Hidden labels may be unsealed after this call."""
        self._frozen = True

    @property
    def is_frozen(self) -> bool:
        return self._frozen

    def get_hidden_status(self, record: CandidateRecord) -> str:
        """Return the hidden status for a record.

        Raises:
            FrozenStateError: If called before ``freeze()``.
        """
        if not self._frozen:
            raise FrozenStateError(
                "Cannot access hidden labels before selection is frozen. "
                "Call CandidateRun.freeze() after winner is selected."
            )
        return record.hidden_status or "unknown"

    def records(self) -> list[CandidateRecord]:
        return list(self._records)


# ---------------------------------------------------------------------------
# Leakage detection
# ---------------------------------------------------------------------------

_FORBIDDEN_HIDDEN_SIGNAL_KEYS: frozenset[str] = frozenset(
    {
        "hidden_pass_fail",
        "hidden_stdout",
        "hidden_stderr",
        "hidden_test_names",
        "prior_hidden_outcome",
    }
)


def _check_no_leakage(selector_input: dict[str, Any]) -> None:
    """Raise LeakageError if selector_input contains any forbidden hidden signal.

    Also detects manual post-hoc choice (selection attempted after hidden
    scoring was unsealed).
    """
    found = sorted(_FORBIDDEN_HIDDEN_SIGNAL_KEYS & selector_input.keys())
    if found:
        raise LeakageError(
            f"Selector input contains forbidden hidden signal(s): {found}"
        )
    if selector_input.get("post_hoc_choice"):
        raise LeakageError(
            "Manual post-hoc choice detected: selection attempted after hidden scoring"
        )


# ---------------------------------------------------------------------------
# Deterministic winner selection
# ---------------------------------------------------------------------------


def _candidate_score(
    record: CandidateRecord,
    tiebreak_order: list[str],
) -> tuple[int | float, ...]:
    """Return a comparable tuple for stable, deterministic selection.

    Higher is better. ``candidate_index`` is negated so the lowest index wins
    ties, producing a stable total order across any input permutation.
    """
    sigs = record.public_signals
    parts: list[int | float] = []
    for key in tiebreak_order:
        if key == "candidate_index":
            parts.append(-record.candidate_index)
        else:
            parts.append(int(bool(sigs.get(key, 0))))
    return tuple(parts)


def select_winner(
    candidates: list[CandidateRecord],
    policy: SelectionPolicy,
    *,
    selector_input: dict[str, Any] | None = None,
) -> CandidateRecord:
    """Select the best candidate using public signals and the policy tie-break order.

    Args:
        candidates: Pool of candidates for a single task.
        policy: The frozen selection policy to apply.
        selector_input: Optional additional signals checked for hidden-signal leakage.

    Returns:
        The winning CandidateRecord.

    Raises:
        LeakageError: If ``selector_input`` contains forbidden hidden signals.
        ValueError: If ``candidates`` is empty.
    """
    if not candidates:
        raise ValueError("No candidates to select from")
    if selector_input is not None:
        _check_no_leakage(selector_input)
    return max(
        candidates,
        key=lambda r: _candidate_score(r, policy.tiebreak_order),
    )


# ---------------------------------------------------------------------------
# Metric recomputation
# ---------------------------------------------------------------------------


def _unbiased_pass_at_k(n: int, c: int, k: int) -> float:
    """Unbiased pass-at-k estimator: 1 - C(n-c, k) / C(n, k).

    Uses the product form to avoid large intermediate factorials::

        1 - prod_{i=0}^{k-1} (n-c-i)/(n-i)

    Args:
        n: Total number of candidates for the task.
        c: Number of passing candidates.
        k: Shot count (must satisfy k <= n).

    Raises:
        ValueError: If n < k.
    """
    if n < k:
        raise ValueError(f"n={n} < k={k}; cannot evaluate {k}-shot coverage")
    if c == 0:
        return 0.0
    if c >= n:
        return 1.0
    num = 1.0
    for i in range(k):
        num *= (n - c - i) / (n - i)
    return 1.0 - num


def compute_metrics(
    records: list[CandidateRecord],
    *,
    k: int | None = None,
) -> dict[str, Any]:
    """Compute all metric artifacts from candidate records.

    Recomputes oracle count, selected count, regret, oracle-lift capture, and
    pass-at-k so that ``pass_at_k.json`` and ``selection_regret.json`` are
    exactly reproducible from ``candidate_records.jsonl``.

    Args:
        records: All candidate records across all tasks.
        k: Shot count for pass-at-k. If None, inferred as the maximum number
           of candidates per task in *records*.

    Returns:
        dict with keys: oracle_count, selected_count, regret_count, regret_rate,
        oracle_lift_capture, pass_at_k, total_tasks.
    """
    # Group by task_id
    tasks: dict[str, list[CandidateRecord]] = {}
    for rec in records:
        tasks.setdefault(rec.task_id, []).append(rec)

    total_tasks = len(tasks)
    if total_tasks == 0:
        return {
            "oracle_count": 0,
            "selected_count": 0,
            "regret_count": 0,
            "regret_rate": 0.0,
            "oracle_lift_capture": None,
            "pass_at_k": 0.0,
            "total_tasks": 0,
        }

    effective_k = k if k is not None else max(len(v) for v in tasks.values())

    oracle_count = 0
    selected_count = 0
    pass_at_k_sum = 0.0
    pass_at_k_n = 0

    for task_recs in tasks.values():
        # Oracle: at least one candidate has a passing public signal
        any_pass = any(
            r.public_signals.get("test_pass", False) for r in task_recs
        )
        if any_pass:
            oracle_count += 1

        # Selected: the marked-selected candidate has a passing public signal
        selected_recs = [r for r in task_recs if r.selected]
        if selected_recs and selected_recs[0].public_signals.get("test_pass", False):
            selected_count += 1

        # pass-at-k: unbiased estimator per task (capped at available candidates)
        n = len(task_recs)
        c = sum(
            1 for r in task_recs if r.public_signals.get("test_pass", False)
        )
        task_k = min(effective_k, n)
        try:
            est = _unbiased_pass_at_k(n, c, task_k)
            pass_at_k_sum += est
            pass_at_k_n += 1
        except ValueError:
            pass  # defensive; should not occur given task_k <= n

    regret_count = oracle_count - selected_count
    regret_rate = regret_count / total_tasks
    oracle_lift: float | None = (
        selected_count / oracle_count if oracle_count > 0 else None
    )
    pass_at_k_val = pass_at_k_sum / pass_at_k_n if pass_at_k_n > 0 else 0.0

    return {
        "oracle_count": oracle_count,
        "selected_count": selected_count,
        "regret_count": regret_count,
        "regret_rate": regret_rate,
        "oracle_lift_capture": oracle_lift,
        "pass_at_k": pass_at_k_val,
        "total_tasks": total_tasks,
    }


# ---------------------------------------------------------------------------
# JSONL artifact I/O
# ---------------------------------------------------------------------------


def write_candidate_records(
    records: list[CandidateRecord],
    output_path: Path,
    *,
    include_hidden: bool = False,
) -> Path:
    """Write candidate records to a JSONL file.

    Args:
        records: Candidate records to write.
        output_path: Destination path (parent directories created as needed).
        include_hidden: Whether to include the ``hidden_status`` field.

    Returns:
        The path written to.
    """
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("w", encoding="utf-8") as fh:
        for record in records:
            fh.write(
                json.dumps(record.to_dict(include_hidden=include_hidden)) + "\n"
            )
    return output_path


def read_candidate_records(path: Path) -> list[CandidateRecord]:
    """Read and validate candidate records from a JSONL file.

    Raises:
        ValueError: If any record is missing required fields.
        TypeError: If ``candidate_index`` is not an integer.
    """
    records: list[CandidateRecord] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        data = json.loads(line)
        validate_candidate_record(data)
        records.append(
            CandidateRecord(
                task_id=data["task_id"],
                arm_id=data["arm_id"],
                candidate_index=data["candidate_index"],
                model=data["model"],
                harness=data["harness"],
                public_signals=data["public_signals"],
                selected=data["selected"],
                hidden_status=data.get("hidden_status"),
            )
        )
    return records
