"""Tests for multi-shot candidate generation and selection artifacts.

Issue: https://github.com/promptdriven/pdd/issues/1475

Covers all 25 test cases from the enhanced test plan:
  1. Selection policy schema and frozen-before-generation requirement
  2. Leakage rejection for all five forbidden hidden input classes
     plus manual post-hoc choice (parametrized)
  3. Deterministic tie-break stability (repeated calls, policy order, n-way)
  4. Candidate record completeness for k > 1
  5. Malformed/missing row detection
  6. Metric recomputation from candidate records
     (oracle, selected, regret, lift, pass-at-k, edge cases)
  7. Golden JSON for all four artifacts
  8. Freeze / hidden-label lifecycle
  9. k=1 degenerate case

No test depends on private RQ corpus rows or hidden verifier output.
All tests use synthetic in-memory records or committed fixtures only.
"""
from __future__ import annotations

import itertools
import json
from pathlib import Path

import jsonschema
import pytest

from pdd.multishot_candidate import (
    SCHEMA_VERSION,
    CandidateRecord,
    CandidateRun,
    FrozenStateError,
    LeakageError,
    SelectionPolicy,
    check_duplicate_candidate_indices,
    compute_metrics,
    read_candidate_records,
    select_winner,
    validate_candidate_record,
    write_candidate_records,
)

# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------

_FIXTURES = Path(__file__).resolve().parent / "fixtures" / "multishot"
_SCHEMA_DIR = Path(__file__).resolve().parents[1] / "pdd" / "schemas"

# ---------------------------------------------------------------------------
# Factories
# ---------------------------------------------------------------------------


def _policy(**kwargs) -> SelectionPolicy:
    """Build a minimal valid SelectionPolicy, optionally overriding fields."""
    base: dict = {
        "schema_version": SCHEMA_VERSION,
        "frozen_before_generation": True,
        "uses_hidden_results": False,
        "trained_on_confirmation_hidden": False,
        "tuned_on_confirmation_hidden": False,
        "training_sources": [
            {
                "name": "public-benchmark-v1",
                "leakage_from_hidden_labels": False,
                "leakage_from_hidden_stdout": False,
                "leakage_from_hidden_test_names": False,
            }
        ],
        "tiebreak_order": ["lint_pass", "parse_ok", "test_pass", "candidate_index"],
    }
    base.update(kwargs)
    return SelectionPolicy(**base)


def _record(
    task_id: str = "task-1",
    arm_id: str = "arm-a",
    candidate_index: int = 0,
    model: str = "test-model-v1",
    harness: str = "pytest-harness",
    public_signals: dict | None = None,
    selected: bool = False,
    hidden_status: str | None = None,
) -> CandidateRecord:
    """Build a minimal valid CandidateRecord."""
    if public_signals is None:
        public_signals = {"lint_pass": 1, "parse_ok": 1, "test_pass": True}
    return CandidateRecord(
        task_id=task_id,
        arm_id=arm_id,
        candidate_index=candidate_index,
        model=model,
        harness=harness,
        public_signals=public_signals,
        selected=selected,
        hidden_status=hidden_status,
    )


def _candidate_schema() -> dict:
    return json.loads(
        (_SCHEMA_DIR / "multishot_candidate.schema.json").read_text(encoding="utf-8")
    )


def _policy_schema() -> dict:
    return json.loads(
        (_SCHEMA_DIR / "selection_policy.schema.json").read_text(encoding="utf-8")
    )


# ---------------------------------------------------------------------------
# Metric test fixture
#
# Layout (for oracle/selected/regret/lift tests):
#   task-1: c0 passes (selected=True)  → oracle: yes, selected: yes
#   task-2: c0 fails, c1 passes        → oracle: yes, selected: no  (regret)
#   task-3: c0 fails, c1 fails         → oracle: no,  selected: no
#
# Expected aggregate metrics:
#   oracle_count   = 2  (task-1, task-2)
#   selected_count = 1  (task-1 only)
#   regret_count   = 1
#   regret_rate    = 1/3 ≈ 0.3333
#   oracle_lift    = 0.5
# ---------------------------------------------------------------------------


def _make_metric_records() -> list[CandidateRecord]:
    """Synthetic candidate records for deterministic metric-recomputation tests."""
    return [
        # task-1: oracle yes, selected yes
        _record(
            "task-1",
            candidate_index=0,
            public_signals={"test_pass": True},
            selected=True,
        ),
        _record(
            "task-1",
            candidate_index=1,
            public_signals={"test_pass": False},
            selected=False,
        ),
        # task-2: oracle yes (c1 passes), selected no (c0 is chosen but fails) → regret
        _record(
            "task-2",
            candidate_index=0,
            public_signals={"test_pass": False},
            selected=True,
        ),
        _record(
            "task-2",
            candidate_index=1,
            public_signals={"test_pass": True},
            selected=False,
        ),
        # task-3: oracle no, selected no
        _record(
            "task-3",
            candidate_index=0,
            public_signals={"test_pass": False},
            selected=True,
        ),
        _record(
            "task-3",
            candidate_index=1,
            public_signals={"test_pass": False},
            selected=False,
        ),
    ]


# ===========================================================================
# Scenario 1: Selection Policy Artifact
# ===========================================================================


def test_selection_policy_schema_valid() -> None:
    """Serialized SelectionPolicy must validate against the JSON schema and carry
    frozen_before_generation=True and uses_hidden_results=False."""
    policy = _policy()
    data = policy.to_dict()
    jsonschema.validate(instance=data, schema=_policy_schema())
    assert data["frozen_before_generation"] is True
    assert data["uses_hidden_results"] is False
    assert data["schema_version"] == SCHEMA_VERSION


def test_selection_policy_training_sources_leakage_flags() -> None:
    """Every training_sources[] entry must carry all three required leakage flag fields."""
    policy = _policy(
        training_sources=[
            {
                "name": "public-corpus-v2",
                "leakage_from_hidden_labels": False,
                "leakage_from_hidden_stdout": False,
                "leakage_from_hidden_test_names": False,
            },
            {
                "name": "synthetic-probes",
                "leakage_from_hidden_labels": False,
                "leakage_from_hidden_stdout": False,
                "leakage_from_hidden_test_names": False,
            },
        ]
    )
    for source in policy.training_sources:
        assert "leakage_from_hidden_labels" in source, (
            f"Missing leakage_from_hidden_labels in source {source['name']}"
        )
        assert "leakage_from_hidden_stdout" in source
        assert "leakage_from_hidden_test_names" in source
        assert isinstance(source["leakage_from_hidden_labels"], bool)
        assert isinstance(source["leakage_from_hidden_stdout"], bool)
        assert isinstance(source["leakage_from_hidden_test_names"], bool)


def test_selection_policy_frozen_before_generation_field() -> None:
    """Constructing SelectionPolicy with frozen_before_generation=False must raise ValueError."""
    with pytest.raises(ValueError, match="frozen_before_generation"):
        _policy(frozen_before_generation=False)


def test_selection_policy_golden_json() -> None:
    """The committed selection_policy.json fixture must round-trip through SelectionPolicy."""
    golden = json.loads(
        (_FIXTURES / "selection_policy.json").read_text(encoding="utf-8")
    )
    policy = SelectionPolicy(**golden)
    assert policy.to_dict() == golden


# ===========================================================================
# Scenario 2: Leakage Rejection (parametrized)
# ===========================================================================

# Each entry: (case_id, selector_input, expected_fragment_in_error_message)
_LEAKAGE_CASES = [
    (
        "hidden_pass_fail",
        {"hidden_pass_fail": True, "lint_pass": 1},
        "hidden_pass_fail",
    ),
    (
        "hidden_stdout",
        {"hidden_stdout": "PASSED 5 tests", "lint_pass": 1},
        "hidden_stdout",
    ),
    (
        "hidden_stderr",
        {"hidden_stderr": "ERROR in test_foo", "lint_pass": 1},
        "hidden_stderr",
    ),
    (
        "hidden_test_names",
        {"hidden_test_names": ["test_foo", "test_bar"], "lint_pass": 1},
        "hidden_test_names",
    ),
    (
        "prior_hidden_outcome",
        {"prior_hidden_outcome": "pass", "lint_pass": 1},
        "prior_hidden_outcome",
    ),
    (
        "manual_post_hoc_choice",
        {"post_hoc_choice": True, "lint_pass": 1},
        "post-hoc",
    ),
]


@pytest.mark.parametrize(
    "case_name,selector_input,expected_msg",
    _LEAKAGE_CASES,
    ids=[c[0] for c in _LEAKAGE_CASES],
)
def test_leakage_rejected(
    case_name: str,
    selector_input: dict,
    expected_msg: str,
) -> None:
    """Each forbidden hidden input class must raise LeakageError before winner is computed."""
    policy = _policy()
    candidates = [_record(selected=False)]
    with pytest.raises(LeakageError, match=expected_msg):
        select_winner(candidates, policy, selector_input=selector_input)


# ===========================================================================
# Scenario 3: Deterministic Tie-Break
# ===========================================================================


def test_deterministic_tie_break_same_winner_repeated_calls() -> None:
    """10 calls with identical tied candidates must always produce the same winner."""
    policy = _policy()
    tied_signals = {"lint_pass": 1, "parse_ok": 1, "test_pass": True}
    c0 = _record(candidate_index=0, public_signals=tied_signals)
    c1 = _record(candidate_index=1, public_signals=tied_signals)

    winners = [
        select_winner([c0, c1], policy).candidate_index for _ in range(10)
    ]
    unique_winners = set(winners)
    assert len(unique_winners) == 1, (
        f"Expected 1 unique winner, got {len(unique_winners)}: {winners}"
    )


def test_deterministic_tie_break_order_from_policy() -> None:
    """Winner must be determined by the first differentiating signal in tiebreak_order."""
    # c0 has lint_pass=1 (first in order); c1 has better parse_ok and test_pass
    policy = _policy(
        tiebreak_order=["lint_pass", "parse_ok", "test_pass", "candidate_index"]
    )
    c0 = _record(
        candidate_index=0,
        public_signals={"lint_pass": 1, "parse_ok": 0, "test_pass": False},
    )
    c1 = _record(
        candidate_index=1,
        public_signals={"lint_pass": 0, "parse_ok": 1, "test_pass": True},
    )

    winner = select_winner([c0, c1], policy)
    assert winner.candidate_index == 0, (
        "c0 should win because lint_pass (first in tiebreak_order) is 1 vs 0"
    )


def test_deterministic_tie_break_n_way_tie() -> None:
    """k=5 identical candidates must produce a stable winner under any input permutation."""
    policy = _policy()
    tied_signals = {"lint_pass": 1, "parse_ok": 1, "test_pass": True}
    candidates = [
        _record(candidate_index=i, public_signals=tied_signals) for i in range(5)
    ]

    # Sample 10 permutations and assert all produce the same winner
    sample_perms = list(itertools.islice(itertools.permutations(candidates), 10))
    winners = {
        select_winner(list(perm), policy).candidate_index for perm in sample_perms
    }
    assert len(winners) == 1, f"Expected stable winner, got distinct winners: {winners}"
    # Lowest candidate_index wins ties (deterministic tiebreak by ascending index)
    assert winners.pop() == 0


# ===========================================================================
# Scenario 4: Candidate Record Completeness
# ===========================================================================


def test_candidate_records_complete_for_all_k() -> None:
    """k=3 synthetic candidates must each have all seven required fields."""
    required_fields = {
        "task_id",
        "arm_id",
        "candidate_index",
        "model",
        "harness",
        "public_signals",
        "selected",
    }
    candidates = [_record(candidate_index=i) for i in range(3)]
    assert len(candidates) == 3
    for rec in candidates:
        row = rec.to_dict()
        missing = required_fields - row.keys()
        assert not missing, f"Record {rec.candidate_index} missing fields: {missing}"


def test_candidate_records_jsonl_schema_valid(tmp_path: Path) -> None:
    """Every JSONL line written by write_candidate_records must validate against the schema."""
    schema = _candidate_schema()
    candidates = [
        _record(
            candidate_index=i,
            public_signals={"lint_pass": 1, "parse_ok": 1, "test_pass": i % 2 == 0},
        )
        for i in range(3)
    ]
    jsonl_path = write_candidate_records(
        candidates, tmp_path / "candidate_records.jsonl"
    )
    for line in jsonl_path.read_text(encoding="utf-8").splitlines():
        if line.strip():
            jsonschema.validate(instance=json.loads(line), schema=schema)


def test_candidate_records_hidden_status_absent_before_freeze() -> None:
    """hidden_status must be absent from the serialized dict before selection is frozen."""
    rec = _record(hidden_status="pass")
    d = rec.to_dict(include_hidden=False)
    assert "hidden_status" not in d, (
        "hidden_status must not appear in JSONL records before selection is frozen"
    )


def test_candidate_records_hidden_status_present_after_freeze() -> None:
    """hidden_status must be present in the serialized dict when include_hidden=True."""
    rec = _record(hidden_status="pass")
    d = rec.to_dict(include_hidden=True)
    assert "hidden_status" in d
    assert d["hidden_status"] == "pass"


# ===========================================================================
# Scenario 5: Malformed/Missing Row Detection
# ===========================================================================


def test_missing_task_id_raises_validation_error() -> None:
    """A record missing task_id must raise ValueError naming the missing field."""
    data = {
        "arm_id": "arm-a",
        "candidate_index": 0,
        "model": "test-model-v1",
        "harness": "pytest-harness",
        "public_signals": {},
        "selected": False,
    }
    with pytest.raises(ValueError, match="task_id"):
        validate_candidate_record(data)


def test_missing_candidate_index_raises_validation_error() -> None:
    """A record missing candidate_index must raise ValueError naming the missing field."""
    data = {
        "task_id": "task-1",
        "arm_id": "arm-a",
        "model": "test-model-v1",
        "harness": "pytest-harness",
        "public_signals": {},
        "selected": False,
    }
    with pytest.raises(ValueError, match="candidate_index"):
        validate_candidate_record(data)


def test_wrong_type_candidate_index_raises() -> None:
    """A candidate_index that is not an integer must raise TypeError."""
    data = {
        "task_id": "task-1",
        "arm_id": "arm-a",
        "candidate_index": "zero",  # should be int
        "model": "test-model-v1",
        "harness": "pytest-harness",
        "public_signals": {},
        "selected": False,
    }
    with pytest.raises(TypeError, match="candidate_index"):
        validate_candidate_record(data)


def test_duplicate_candidate_index_raises() -> None:
    """Duplicate (task_id, candidate_index) pairs must raise ValueError."""
    c0a = _record(task_id="task-1", candidate_index=0)
    c0b = _record(task_id="task-1", candidate_index=0)  # duplicate
    with pytest.raises(ValueError, match="Duplicate"):
        check_duplicate_candidate_indices([c0a, c0b])


# ===========================================================================
# Scenario 6: Metric Recomputation
# ===========================================================================


def test_oracle_count_recomputation() -> None:
    """Oracle count = number of tasks where at least one candidate passes."""
    records = _make_metric_records()
    metrics = compute_metrics(records)
    # task-1: c0 passes → oracle; task-2: c1 passes → oracle; task-3: none pass
    assert metrics["oracle_count"] == 2


def test_selected_count_recomputation() -> None:
    """Selected count = number of tasks where the chosen candidate passes."""
    records = _make_metric_records()
    metrics = compute_metrics(records)
    # task-1 selected c0 (pass); task-2 selected c0 (fail); task-3 selected c0 (fail)
    assert metrics["selected_count"] == 1


def test_regret_count_and_rate() -> None:
    """regret_count == oracle_count - selected_count; regret_rate == regret_count / total."""
    records = _make_metric_records()
    metrics = compute_metrics(records)
    assert metrics["regret_count"] == metrics["oracle_count"] - metrics["selected_count"]
    assert metrics["regret_rate"] == pytest.approx(
        metrics["regret_count"] / metrics["total_tasks"]
    )


def test_oracle_lift_capture() -> None:
    """Oracle lift = selected_count / oracle_count; None when oracle_count == 0."""
    records = _make_metric_records()
    metrics = compute_metrics(records)
    expected_lift = metrics["selected_count"] / metrics["oracle_count"]
    assert metrics["oracle_lift_capture"] == pytest.approx(expected_lift)

    # Edge case: oracle_count == 0 → lift is undefined (None)
    all_fail = [
        _record(
            "task-x",
            candidate_index=0,
            public_signals={"test_pass": False},
            selected=True,
        )
    ]
    zero_oracle = compute_metrics(all_fail)
    assert zero_oracle["oracle_lift_capture"] is None


def test_pass_at_k_recomputation_unbiased() -> None:
    """pass_at_k must match the unbiased estimator computed directly from records."""
    records = _make_metric_records()
    metrics = compute_metrics(records, k=2)

    # Manual unbiased estimates:
    # task-1: n=2, c=1, k=2 → 1 − (1/2 × 0/1) = 1.0
    # task-2: n=2, c=1, k=2 → 1.0  (same n, c, k)
    # task-3: n=2, c=0, k=2 → 0.0
    expected = (1.0 + 1.0 + 0.0) / 3
    assert metrics["pass_at_k"] == pytest.approx(expected, abs=1e-9)


def test_pass_at_k_edge_case_k1() -> None:
    """With k=1, the unbiased estimator reduces to the per-task pass/fail indicator."""
    records = [
        _record(
            "task-A",
            candidate_index=0,
            public_signals={"test_pass": True},
            selected=True,
        ),
        _record(
            "task-B",
            candidate_index=0,
            public_signals={"test_pass": False},
            selected=True,
        ),
    ]
    metrics = compute_metrics(records, k=1)
    # task-A: n=1, c=1, k=1 → 1.0;  task-B: n=1, c=0, k=1 → 0.0
    assert metrics["pass_at_k"] == pytest.approx(0.5, abs=1e-9)


def test_pass_at_k_edge_case_all_pass() -> None:
    """pass_at_k == 1.0 when every candidate of every task passes."""
    records = [
        _record(
            f"task-{i}",
            candidate_index=j,
            public_signals={"test_pass": True},
            selected=(j == 0),
        )
        for i in range(3)
        for j in range(2)
    ]
    metrics = compute_metrics(records, k=2)
    assert metrics["pass_at_k"] == pytest.approx(1.0, abs=1e-9)


def test_pass_at_k_edge_case_all_fail() -> None:
    """pass_at_k == 0.0 when every candidate of every task fails."""
    records = [
        _record(
            f"task-{i}",
            candidate_index=j,
            public_signals={"test_pass": False},
            selected=(j == 0),
        )
        for i in range(3)
        for j in range(2)
    ]
    metrics = compute_metrics(records, k=2)
    assert metrics["pass_at_k"] == pytest.approx(0.0, abs=1e-9)


# ===========================================================================
# Scenario 7: Golden JSON — All Four Artifacts
# ===========================================================================


def test_golden_selection_policy_json() -> None:
    """Committed selection_policy.json must be schema-valid and have correct flag values."""
    schema = _policy_schema()
    golden_data = json.loads(
        (_FIXTURES / "selection_policy.json").read_text(encoding="utf-8")
    )
    jsonschema.validate(instance=golden_data, schema=schema)
    assert golden_data["frozen_before_generation"] is True
    assert golden_data["uses_hidden_results"] is False
    assert golden_data["schema_version"] == SCHEMA_VERSION


def test_golden_candidate_records_jsonl() -> None:
    """Every line of committed candidate_records.jsonl must validate against the schema."""
    schema = _candidate_schema()
    jsonl_text = (_FIXTURES / "candidate_records.jsonl").read_text(encoding="utf-8")
    lines_validated = 0
    for line in jsonl_text.splitlines():
        if line.strip():
            jsonschema.validate(instance=json.loads(line), schema=schema)
            lines_validated += 1
    assert lines_validated > 0, "candidate_records.jsonl must contain at least one record"


def test_golden_pass_at_k_json() -> None:
    """pass_at_k.json must be exactly recomputable from the committed candidate_records.jsonl."""
    records = read_candidate_records(_FIXTURES / "candidate_records.jsonl")
    golden = json.loads((_FIXTURES / "pass_at_k.json").read_text(encoding="utf-8"))
    computed = compute_metrics(records, k=golden["k"])
    assert computed["pass_at_k"] == pytest.approx(golden["pass_at_k"], abs=1e-9)
    assert computed["total_tasks"] == golden["total_tasks"]


def test_golden_selection_regret_json() -> None:
    """selection_regret.json must be exactly recomputable from candidate_records.jsonl."""
    records = read_candidate_records(_FIXTURES / "candidate_records.jsonl")
    golden = json.loads(
        (_FIXTURES / "selection_regret.json").read_text(encoding="utf-8")
    )
    computed = compute_metrics(records)
    assert computed["oracle_count"] == golden["oracle_count"]
    assert computed["selected_count"] == golden["selected_count"]
    assert computed["regret_count"] == golden["regret_count"]
    assert computed["regret_rate"] == pytest.approx(golden["regret_rate"], abs=1e-9)
    assert computed["total_tasks"] == golden["total_tasks"]
    oracle_lift = golden.get("oracle_lift_capture")
    if oracle_lift is None:
        assert computed["oracle_lift_capture"] is None
    else:
        assert computed["oracle_lift_capture"] == pytest.approx(oracle_lift, abs=1e-9)


# ===========================================================================
# Scenario 8: Freeze / Hidden-Label Lifecycle
# ===========================================================================


def test_hidden_labels_raise_before_freeze() -> None:
    """Accessing hidden labels via CandidateRun before freeze() must raise FrozenStateError."""
    policy = _policy()
    run = CandidateRun(policy)
    rec = _record(hidden_status="pass")
    run.add_record(rec)

    assert not run.is_frozen
    with pytest.raises(FrozenStateError):
        run.get_hidden_status(rec)


def test_hidden_labels_accessible_after_freeze() -> None:
    """After freeze() is called, get_hidden_status() must return the stored status."""
    policy = _policy()
    run = CandidateRun(policy)
    rec = _record(hidden_status="pass")
    run.add_record(rec)

    run.freeze()
    assert run.is_frozen
    assert run.get_hidden_status(rec) == "pass"


# ===========================================================================
# Scenario 9: k=1 Degenerate Case
# ===========================================================================


def test_k1_single_candidate_always_selected() -> None:
    """With k=1, the sole candidate is selected; regret_count is 0."""
    policy = _policy()
    candidates = [
        _record(
            candidate_index=0,
            public_signals={"test_pass": True},
            selected=True,
        )
    ]
    winner = select_winner(candidates, policy)
    assert winner.candidate_index == 0

    metrics = compute_metrics(candidates, k=1)
    assert metrics["regret_count"] == 0
    assert metrics["total_tasks"] == 1


def test_k1_pass_at_1_equals_pass_rate() -> None:
    """With k=1, pass-at-1 must equal the fraction of tasks where the single candidate passes."""
    records = [
        _record(
            "task-1",
            candidate_index=0,
            public_signals={"test_pass": True},
            selected=True,
        ),
        _record(
            "task-2",
            candidate_index=0,
            public_signals={"test_pass": True},
            selected=True,
        ),
        _record(
            "task-3",
            candidate_index=0,
            public_signals={"test_pass": False},
            selected=True,
        ),
    ]
    metrics = compute_metrics(records, k=1)
    # 2 out of 3 tasks pass → pass-at-1 = 2/3
    assert metrics["pass_at_k"] == pytest.approx(2 / 3, abs=1e-9)
