"""Unit tests for per-task config routing + multi-shot in llm_invoke (#1584).

The whole feature is gated behind PDD_ENABLE_TASK_ROUTING=1. These tests cover
the router scoring/selection logic, the multi-shot loop's candidate selection,
the env guards, and the flag-off no-op behavior. They mock the underlying
single-shot invocation so no provider credentials are required.
"""

import importlib

import pytest

import pdd.llm_invoke as m


@pytest.fixture(autouse=True)
def _reset_routing_state(monkeypatch):
    """Clear the module-level routing cache and routing env vars per test."""
    m._TASK_ROUTING_TABLE = None
    for var in ("PDD_ENABLE_TASK_ROUTING", "PDD_ROUTER_LAMBDA"):
        monkeypatch.delenv(var, raising=False)
    yield
    m._TASK_ROUTING_TABLE = None


# --------------------------------------------------------------------------- #
# _effort_to_time
# --------------------------------------------------------------------------- #
@pytest.mark.parametrize(
    "effort,expected",
    [
        ("low", 0.1),
        ("medium", 0.3),
        ("high", 0.5),
        ("xhigh", 0.75),
        ("max", 1.0),
        ("HIGH", 0.5),
        ("  low  ", 0.1),
        ("bogus", None),
        (None, None),
        ("", None),
    ],
)
def test_effort_to_time(effort, expected):
    assert m._effort_to_time(effort) == expected


# --------------------------------------------------------------------------- #
# _select_task_route
# --------------------------------------------------------------------------- #
def _stub_table(monkeypatch, rows):
    monkeypatch.setattr(m, "_load_task_routing_table", lambda *a, **k: rows)


def test_select_route_none_task_class():
    assert m._select_task_route(None) is None


def test_select_route_cold_start_no_match(monkeypatch):
    _stub_table(monkeypatch, [{"task_class": "fix", "model": "x", "pass_rate": "0.9",
                               "avg_cost_usd": "0.1", "temperature": "0.2",
                               "effort": "low", "shots": "1"}])
    assert m._select_task_route("generate") is None


def test_select_route_empty_table(monkeypatch):
    _stub_table(monkeypatch, [])
    assert m._select_task_route("generate") is None


def test_select_route_picks_highest_score(monkeypatch):
    rows = [
        {"task_class": "generate", "model": "cheap", "temperature": "0.0",
         "effort": "low", "shots": "1", "pass_rate": "0.70", "avg_cost_usd": "0.10"},
        {"task_class": "generate", "model": "strong", "temperature": "0.2",
         "effort": "high", "shots": "2", "pass_rate": "0.95", "avg_cost_usd": "0.20"},
    ]
    _stub_table(monkeypatch, rows)
    # lambda=1.0 -> cheap=0.60, strong=0.75 -> strong wins.
    route = m._select_task_route("generate")
    assert route["model"] == "strong"
    assert route["temperature"] == 0.2
    assert route["shots"] == 2
    assert route["effort"] == "high"


def test_select_route_lambda_changes_winner(monkeypatch):
    rows = [
        {"task_class": "generate", "model": "cheap", "temperature": "0.0",
         "effort": "low", "shots": "1", "pass_rate": "0.70", "avg_cost_usd": "0.10"},
        {"task_class": "generate", "model": "strong", "temperature": "0.2",
         "effort": "high", "shots": "2", "pass_rate": "0.95", "avg_cost_usd": "0.20"},
    ]
    _stub_table(monkeypatch, rows)
    # High lambda penalizes the costlier strong model: cheap=0.70-2*0.10=0.50,
    # strong=0.95-2*0.20=0.55 -> still strong; push lambda higher.
    monkeypatch.setenv("PDD_ROUTER_LAMBDA", "3.0")
    # cheap=0.70-3*0.10=0.40, strong=0.95-3*0.20=0.35 -> cheap wins.
    assert m._select_task_route("generate")["model"] == "cheap"


def test_select_route_invalid_lambda_defaults_to_one(monkeypatch):
    rows = [
        {"task_class": "generate", "model": "cheap", "temperature": "0.0",
         "effort": "low", "shots": "1", "pass_rate": "0.70", "avg_cost_usd": "0.10"},
        {"task_class": "generate", "model": "strong", "temperature": "0.2",
         "effort": "high", "shots": "2", "pass_rate": "0.95", "avg_cost_usd": "0.20"},
    ]
    _stub_table(monkeypatch, rows)
    monkeypatch.setenv("PDD_ROUTER_LAMBDA", "not-a-number")
    # Falls back to lambda=1.0 -> strong wins.
    assert m._select_task_route("generate")["model"] == "strong"


def test_select_route_tiebreak_lowest_cost(monkeypatch):
    rows = [
        {"task_class": "fix", "model": "a", "temperature": "0.1", "effort": "low",
         "shots": "1", "pass_rate": "0.80", "avg_cost_usd": "0.20"},
        {"task_class": "fix", "model": "b", "temperature": "0.1", "effort": "low",
         "shots": "1", "pass_rate": "0.70", "avg_cost_usd": "0.10"},
    ]
    _stub_table(monkeypatch, rows)
    # lambda=1.0 -> a=0.60, b=0.60 tie -> lowest cost (b) wins.
    assert m._select_task_route("fix")["model"] == "b"


def test_select_route_swallows_errors(monkeypatch):
    rows = [{"task_class": "generate", "model": "x", "pass_rate": "not-a-float",
             "avg_cost_usd": "0.1"}]
    _stub_table(monkeypatch, rows)
    # Malformed numeric data must not raise; route falls through to baseline.
    assert m._select_task_route("generate") is None


# --------------------------------------------------------------------------- #
# _load_task_routing_table
# --------------------------------------------------------------------------- #
def test_load_table_reads_and_caches(monkeypatch, tmp_path):
    csv_file = tmp_path / "task_routing.csv"
    csv_file.write_text(
        "task_class,model,temperature,effort,shots,pass_rate,avg_cost_usd\n"
        "generate,anthropic/claude-sonnet-4-6,0.1,low,1,0.9,0.05\n"
    )
    monkeypatch.setattr(m, "_resolve_task_routing_csv", lambda: csv_file)
    rows = m._load_task_routing_table(force_reload=True)
    assert len(rows) == 1
    assert rows[0]["task_class"] == "generate"
    # Cached on the second call (sentinel rows returned verbatim).
    m._TASK_ROUTING_TABLE = [{"sentinel": "1"}]
    assert m._load_task_routing_table() == [{"sentinel": "1"}]


def test_load_table_missing_file_returns_empty(monkeypatch):
    monkeypatch.setattr(m, "_resolve_task_routing_csv", lambda: None)
    monkeypatch.setattr(
        m.importlib.resources, "files",
        lambda *a, **k: (_ for _ in ()).throw(FileNotFoundError("nope")),
    )
    assert m._load_task_routing_table(force_reload=True) == []


# --------------------------------------------------------------------------- #
# _run_multishot
# --------------------------------------------------------------------------- #
def _fake_llm(monkeypatch, results):
    """Patch the module-level llm_invoke that _run_multishot calls."""
    calls = {"n": 0}

    def fake(**kwargs):
        r = results[calls["n"]]
        calls["n"] += 1
        return r

    monkeypatch.setattr(m, "llm_invoke", fake)
    return calls


def test_multishot_verifier_first_pass_wins(monkeypatch):
    results = [
        {"result": "bad1", "cost": 0.01, "model_name": "x"},
        {"result": "good", "cost": 0.02, "model_name": "x"},
        {"result": "bad2", "cost": 0.04, "model_name": "x"},
    ]
    _fake_llm(monkeypatch, results)
    out = m._run_multishot(
        shots=3, verifier=lambda s: s == "good", model_override=None,
        prompt="p", input_json={}, strength=0.5, temperature=0.1, verbose=False,
        output_pydantic=None, output_schema=None, time=0.25, use_batch_mode=False,
        messages=None, language=None, use_cloud=False, grounding_overrides=None,
        source_prompt=None, estimate_only=None,
    )
    assert out["result"] == "good"
    # Stops at the first passing candidate -> cost is shot1 + shot2 only.
    assert out["cost"] == pytest.approx(0.03)


def test_multishot_self_consistency_mode_fallback(monkeypatch):
    results = [
        {"result": "A", "cost": 0.01},
        {"result": "B", "cost": 0.01},
        {"result": "B", "cost": 0.01},
    ]
    _fake_llm(monkeypatch, results)
    out = m._run_multishot(
        shots=3, verifier=None, model_override=None,
        prompt="p", input_json={}, strength=0.5, temperature=0.1, verbose=False,
        output_pydantic=None, output_schema=None, time=0.25, use_batch_mode=False,
        messages=None, language=None, use_cloud=False, grounding_overrides=None,
        source_prompt=None, estimate_only=None,
    )
    assert out["result"] == "B"  # mode
    assert out["cost"] == pytest.approx(0.03)  # all shots summed


def test_multishot_verifier_never_passes_falls_back_to_mode(monkeypatch):
    results = [
        {"result": "X", "cost": 0.01},
        {"result": "X", "cost": 0.01},
        {"result": "Y", "cost": 0.01},
    ]
    _fake_llm(monkeypatch, results)
    out = m._run_multishot(
        shots=3, verifier=lambda s: False, model_override=None,
        prompt="p", input_json={}, strength=0.5, temperature=0.1, verbose=False,
        output_pydantic=None, output_schema=None, time=0.25, use_batch_mode=False,
        messages=None, language=None, use_cloud=False, grounding_overrides=None,
        source_prompt=None, estimate_only=None,
    )
    assert out["result"] == "X"


def test_multishot_tiebreak_first_occurrence(monkeypatch):
    results = [
        {"result": "first", "cost": 0.0},
        {"result": "second", "cost": 0.0},
    ]
    _fake_llm(monkeypatch, results)
    out = m._run_multishot(
        shots=2, verifier=None, model_override=None,
        prompt="p", input_json={}, strength=0.5, temperature=0.1, verbose=False,
        output_pydantic=None, output_schema=None, time=0.25, use_batch_mode=False,
        messages=None, language=None, use_cloud=False, grounding_overrides=None,
        source_prompt=None, estimate_only=None,
    )
    assert out["result"] == "first"  # 1-1 tie -> earliest


def test_multishot_passes_model_override_via_contextvar(monkeypatch):
    seen = []

    def fake(**kwargs):
        seen.append(m._ROUTER_MODEL_OVERRIDE.get())
        return {"result": "ok", "cost": 0.0}

    monkeypatch.setattr(m, "llm_invoke", fake)
    m._run_multishot(
        shots=2, verifier=None, model_override="anthropic/claude-haiku-4-5",
        prompt="p", input_json={}, strength=0.5, temperature=0.1, verbose=False,
        output_pydantic=None, output_schema=None, time=0.25, use_batch_mode=False,
        messages=None, language=None, use_cloud=False, grounding_overrides=None,
        source_prompt=None, estimate_only=None,
    )
    assert seen == ["anthropic/claude-haiku-4-5", "anthropic/claude-haiku-4-5"]
    # Context var is reset after the loop.
    assert m._ROUTER_MODEL_OVERRIDE.get() is None


# --------------------------------------------------------------------------- #
# llm_invoke dispatch / guards
# --------------------------------------------------------------------------- #
def test_flag_off_ignores_shots(monkeypatch):
    """With the flag unset, shots>1 must NOT trigger the multi-shot loop."""
    multishot_called = {"v": False}
    monkeypatch.setattr(
        m, "_run_multishot",
        lambda **k: multishot_called.__setitem__("v", True) or {"result": "x"},
    )

    class _Sentinel(Exception):
        pass

    # Reaching model selection proves the single-shot path was taken.
    monkeypatch.setattr(
        m, "_select_model_candidates",
        lambda *a, **k: (_ for _ in ()).throw(_Sentinel()),
    )
    monkeypatch.setattr(m, "_load_model_data", lambda *a, **k: object())
    with pytest.raises(_Sentinel):
        m.llm_invoke(prompt="p", input_json={}, shots=4, use_cloud=False)
    assert multishot_called["v"] is False


def test_flag_on_dispatches_and_clamps_shots(monkeypatch):
    captured = {}
    monkeypatch.setenv("PDD_ENABLE_TASK_ROUTING", "1")
    monkeypatch.setattr(m, "_select_task_route", lambda tc: None)
    monkeypatch.setattr(
        m, "_run_multishot",
        lambda **k: captured.update(k) or {"result": "done", "cost": 0.0},
    )
    out = m.llm_invoke(prompt="p", input_json={}, shots=99, use_cloud=False)
    assert out["result"] == "done"
    assert captured["shots"] == 5  # clamped to the hard cap


def test_flag_on_batch_plus_shots_raises(monkeypatch):
    monkeypatch.setenv("PDD_ENABLE_TASK_ROUTING", "1")
    with pytest.raises(ValueError, match="mutually exclusive"):
        m.llm_invoke(
            messages=[[{"role": "user", "content": "hi"}]],
            use_batch_mode=True,
            shots=2,
            use_cloud=False,
        )


def test_flag_on_router_overrides_model(monkeypatch):
    """A matched route's model must reach model selection as the base model."""
    monkeypatch.setenv("PDD_ENABLE_TASK_ROUTING", "1")
    monkeypatch.setattr(
        m, "_select_task_route",
        lambda tc: {"model": "anthropic/claude-opus-4-8", "temperature": 0.0,
                    "shots": 1, "effort": "high"},
    )
    seen = {}

    class _Sentinel(Exception):
        pass

    def fake_select(strength, base_model, df):
        seen["base_model"] = base_model
        raise _Sentinel()

    monkeypatch.setattr(m, "_load_model_data", lambda *a, **k: object())
    monkeypatch.setattr(m, "_select_model_candidates", fake_select)
    with pytest.raises(_Sentinel):
        m.llm_invoke(prompt="p", input_json={}, task_class="generate", use_cloud=False)
    assert seen["base_model"] == "anthropic/claude-opus-4-8"
