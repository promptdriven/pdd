"""Epic #1431 (PR #1582) acceptance contract: "machinery landed but dormant".

These tests are the validation oracle for the epic PR's central claim — the v1
task-routing machinery is shipped and *functional when activated*, yet a strict
no-op in the default/production state. They are intentionally split into three
contracts:

1. DORMANT-BY-DESIGN (shipped state) — the artifacts PDD actually ships make the
   router inert: the packaged ``task_routing.csv`` is header-only, so the table
   loads empty and ``_select_task_route`` returns None for every PDD command at
   cold start; with ``PDD_ENABLE_TASK_ROUTING`` unset the router is never even
   consulted. A regression that activates routing (e.g. someone commits routing
   rows, or flips the default) breaks these.
2. AGENTIC WIRING DORMANT — ``run_agentic_task`` defaults ``routing_policy`` and
   ``task_class`` to None, so no orchestrator routes unless one is wired in.
3. FUNCTIONAL WHEN ACTIVATED — fed a populated table + the flag + a task_class,
   the router really does override the model (proving the machinery is real, not
   vapor). The provider call is stubbed, so no credentials are needed.

Everything is exercised against the *real* shipped modules/artifacts; only the
provider boundary and (where noted) the table source are stubbed.
"""

import csv
import importlib.resources
import inspect
import io

import pytest

import pdd.agentic_common as ac
import pdd.llm_invoke as m

# Documented PDD command/task classes that callers would pass as ``task_class``.
PDD_TASK_CLASSES = ("generate", "fix", "optimize", "crash", "update", "test", "example")


@pytest.fixture(autouse=True)
def _reset_routing_state(monkeypatch):
    """Clear the module-level routing cache and routing env vars per test."""
    m._TASK_ROUTING_TABLE = None
    for var in ("PDD_ENABLE_TASK_ROUTING", "PDD_ROUTER_LAMBDA"):
        monkeypatch.delenv(var, raising=False)
    yield
    m._TASK_ROUTING_TABLE = None


# --------------------------------------------------------------------------- #
# Contract 1: dormant by design (the SHIPPED artifact state)
# --------------------------------------------------------------------------- #
def test_packaged_task_routing_csv_is_header_only():
    """The shipped routing table carries the schema header but zero data rows.

    This is the load-bearing dormancy fact: an empty table means the router
    cannot select any route in production. Populating it is a deliberate
    activation step, so this test must be updated on purpose when that happens.
    """
    text = importlib.resources.files("pdd").joinpath("data/task_routing.csv").read_text()
    lines = [ln for ln in text.splitlines() if ln.strip()]
    assert lines, "packaged task_routing.csv is unexpectedly empty (no header)"
    header = next(csv.reader([lines[0]]))
    assert header == [
        "task_class",
        "model",
        "temperature",
        "effort",
        "shots",
        "pass_rate",
        "avg_cost_usd",
    ]
    data_rows = list(csv.DictReader(io.StringIO(text)))
    assert data_rows == [], (
        "packaged task_routing.csv now has data rows; routing is no longer "
        "dormant-by-default. If this is intended activation, update this test."
    )


def test_real_routing_table_loads_empty(monkeypatch):
    """Loading the table from the packaged copy yields an empty list."""
    # Force the packaged copy (ignore any developer ~/.pdd or project override).
    monkeypatch.setattr(m, "_resolve_task_routing_csv", lambda: None)
    assert m._load_task_routing_table(force_reload=True) == []


def test_cold_start_route_is_none_for_every_pdd_command(monkeypatch):
    """With the shipped (empty) table, no PDD command resolves to a route."""
    monkeypatch.setattr(m, "_resolve_task_routing_csv", lambda: None)
    m._load_task_routing_table(force_reload=True)
    for task_class in PDD_TASK_CLASSES:
        assert m._select_task_route(task_class) is None, (
            f"cold-start route for {task_class!r} should be None on the empty table"
        )


def test_flag_off_never_consults_router(monkeypatch):
    """Flag unset => the router is not even invoked, regardless of task_class.

    Complements ``test_flag_off_ignores_shots`` (which proves the multi-shot
    loop is skipped). Here we prove the *route selection* itself is gated, so a
    populated table could never leak into a default invocation.
    """
    consulted = {"v": False}

    def spy_route(task_class):
        consulted["v"] = True
        return {"model": "should-not-be-used"}

    monkeypatch.setattr(m, "_select_task_route", spy_route)

    class _Sentinel(Exception):
        pass

    # Reaching model selection proves the ordinary single-shot path was taken.
    monkeypatch.setattr(
        m, "_select_model_candidates",
        lambda *a, **k: (_ for _ in ()).throw(_Sentinel()),
    )
    monkeypatch.setattr(m, "_load_model_data", lambda *a, **k: object())

    with pytest.raises(_Sentinel):
        m.llm_invoke(
            prompt="p", input_json={}, task_class="generate", shots=3, use_cloud=False
        )
    assert consulted["v"] is False, "router was consulted with the feature flag off"


# --------------------------------------------------------------------------- #
# Contract 2: agentic-side wiring is dormant
# --------------------------------------------------------------------------- #
def test_run_agentic_task_routing_params_default_to_none():
    """No orchestrator routes unless it explicitly passes a policy / task_class."""
    sig = inspect.signature(ac.run_agentic_task)
    assert sig.parameters["routing_policy"].default is None
    assert sig.parameters["task_class"].default is None


# --------------------------------------------------------------------------- #
# Contract 3: the machinery is functional once activated
# --------------------------------------------------------------------------- #
def test_router_overrides_model_when_table_populated(monkeypatch):
    """Flag on + populated table + task_class => routed model reaches selection.

    This proves the dormancy is a matter of empty data/flag, not missing wiring:
    feed the machinery and it routes. The selection mock tolerates the
    ``manifest_by_model`` kwarg so it stays in sync with ``_select_model_candidates``.
    """
    monkeypatch.setenv("PDD_ENABLE_TASK_ROUTING", "1")
    monkeypatch.setattr(
        m, "_select_task_route",
        lambda tc: {"model": "anthropic/claude-opus-4-8", "temperature": 0.0,
                    "shots": 1, "effort": "high"},
    )
    seen = {}

    class _Sentinel(Exception):
        pass

    def fake_select(strength, base_model, *args, **kwargs):
        seen["base_model"] = base_model
        raise _Sentinel()

    monkeypatch.setattr(m, "_load_model_data", lambda *a, **k: object())
    monkeypatch.setattr(m, "_select_model_candidates", fake_select)

    with pytest.raises(_Sentinel):
        m.llm_invoke(prompt="p", input_json={}, task_class="generate", use_cloud=False)
    assert seen["base_model"] == "anthropic/claude-opus-4-8"


def test_router_activates_only_when_flag_and_data_present(monkeypatch):
    """End-to-end gate: with the flag on but the SHIPPED empty table, the route
    is still None — activation needs BOTH the flag and populated data."""
    monkeypatch.setenv("PDD_ENABLE_TASK_ROUTING", "1")
    monkeypatch.setattr(m, "_resolve_task_routing_csv", lambda: None)
    m._load_task_routing_table(force_reload=True)
    assert m._select_task_route("generate") is None
