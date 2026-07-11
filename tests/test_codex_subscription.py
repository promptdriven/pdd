"""Tests for the ChatGPT/Codex subscription fallback (issue #1269).

Covers the two seams the feature dies at if wrong:
  * reachability — a `chatgpt/` CSV row is actually reached by the candidate
    loop when ``ANTHROPIC_API_KEY`` is unavailable, and
  * the credential gate / auth bridge / structured-output coercion behave.

All LLM calls are mocked — no real network/LLM access.
"""

import json
import os
from pathlib import Path
from unittest.mock import patch

import pandas as pd
import pytest

import pdd.codex_subscription as cs
import pdd.llm_invoke as li


# --------------------------------------------------------------------------- #
# codex_subscription module: flatten / bridge / detect
# --------------------------------------------------------------------------- #

def _nested_auth(access="acc-tok-AAAAAAAAAA", refresh="ref-tok", acct="uuid-1"):
    return {
        "auth_mode": "chatgpt",
        "OPENAI_API_KEY": "sk-ignored",
        "tokens": {
            "id_token": "id-jwt",
            "access_token": access,
            "refresh_token": refresh,
            "account_id": acct,
        },
        "last_refresh": "2026-05-29T00:00:00Z",
    }


def test_flatten_nested_codex_tokens():
    flat = cs._flatten_codex_tokens(_nested_auth())
    assert flat == {
        "access_token": "acc-tok-AAAAAAAAAA",
        "refresh_token": "ref-tok",
        "id_token": "id-jwt",
        "account_id": "uuid-1",
    }


def test_flatten_accepts_already_flat_shape():
    flat = cs._flatten_codex_tokens({"access_token": "x" * 12, "account_id": "a"})
    assert flat["access_token"] == "x" * 12


def test_flatten_returns_none_without_access_token():
    assert cs._flatten_codex_tokens({"tokens": {"refresh_token": "r"}}) is None
    assert cs._flatten_codex_tokens({}) is None
    assert cs._flatten_codex_tokens("nope") is None


@pytest.fixture
def codex_env(tmp_path, monkeypatch):
    """Isolated CODEX_HOME + bridged dir; clears any inherited CHATGPT_TOKEN_DIR."""
    codex_home = tmp_path / "codex"
    codex_home.mkdir()
    bridged = tmp_path / "bridged"
    monkeypatch.setenv("CODEX_HOME", str(codex_home))
    monkeypatch.setenv("PDD_CHATGPT_TOKEN_DIR", str(bridged))
    monkeypatch.delenv("CHATGPT_TOKEN_DIR", raising=False)
    monkeypatch.delenv("CHATGPT_AUTH_FILE", raising=False)
    return codex_home, bridged


def test_bridge_writes_flattened_auth_and_sets_env(codex_env):
    codex_home, bridged = codex_env
    (codex_home / "auth.json").write_text(json.dumps(_nested_auth()))

    assert cs.bridge_codex_auth_for_litellm() is True
    staged = bridged / "auth.json"
    assert staged.is_file()
    data = json.loads(staged.read_text())
    assert data["access_token"] == "acc-tok-AAAAAAAAAA"
    assert "tokens" not in data  # flattened
    assert os.environ["CHATGPT_TOKEN_DIR"] == str(bridged)
    # 0600 perms on the secret file
    assert (staged.stat().st_mode & 0o077) == 0


def test_bridge_returns_false_when_no_codex_token(codex_env):
    assert cs.bridge_codex_auth_for_litellm() is False


def test_bridge_refreshes_when_source_rotates(codex_env):
    codex_home, bridged = codex_env
    src = codex_home / "auth.json"
    src.write_text(json.dumps(_nested_auth(access="old-token-1")))
    assert cs.bridge_codex_auth_for_litellm() is True
    assert json.loads((bridged / "auth.json").read_text())["access_token"] == "old-token-1"

    # Rotate the source with a strictly newer mtime; bridge must re-stage.
    src.write_text(json.dumps(_nested_auth(access="new-token-2")))
    os.utime(src, (10**10, 10**10))
    assert cs.bridge_codex_auth_for_litellm() is True
    assert json.loads((bridged / "auth.json").read_text())["access_token"] == "new-token-2"


def test_bridge_respects_user_supplied_token_dir(tmp_path, monkeypatch):
    user_dir = tmp_path / "userchatgpt"
    user_dir.mkdir()
    (user_dir / "auth.json").write_text(json.dumps({"access_token": "u" * 12}))
    monkeypatch.setenv("CHATGPT_TOKEN_DIR", str(user_dir))
    monkeypatch.delenv("CODEX_HOME", raising=False)
    assert cs.bridge_codex_auth_for_litellm() is True
    # User dir untouched / still authoritative.
    assert os.environ["CHATGPT_TOKEN_DIR"] == str(user_dir)


def test_has_codex_subscription_auth(codex_env):
    codex_home, _ = codex_env
    assert cs.has_codex_subscription_auth() is False
    (codex_home / "auth.json").write_text(json.dumps(_nested_auth()))
    assert cs.has_codex_subscription_auth() is True


def test_is_chatgpt_subscription_model():
    assert cs.is_chatgpt_subscription_model("chatgpt/gpt-5.3-codex")
    assert not cs.is_chatgpt_subscription_model("claude-sonnet-4-6")
    assert not cs.is_chatgpt_subscription_model(None)


def test_schema_instruction_contains_json_and_only_directive():
    instr = cs.build_chatgpt_schema_instruction({"type": "object", "properties": {}})
    assert "JSON" in instr
    assert "ONLY" in instr
    assert '"type": "object"' in instr


# --------------------------------------------------------------------------- #
# _ensure_api_key: chatgpt/ credential gate
# --------------------------------------------------------------------------- #

def _chatgpt_row():
    return {"model": "chatgpt/gpt-5.3-codex", "api_key": "", "provider": "OpenAI ChatGPT"}


def test_ensure_api_key_chatgpt_ok_when_bridge_succeeds(monkeypatch):
    monkeypatch.setenv("PDD_FORCE", "1")
    with patch.object(li, "_ensure_api_key", wraps=li._ensure_api_key):
        with patch("pdd.codex_subscription.bridge_codex_auth_for_litellm", return_value=True):
            assert li._ensure_api_key(_chatgpt_row(), {}, False) is True


def test_ensure_api_key_chatgpt_skipped_in_force_without_auth(monkeypatch):
    monkeypatch.setenv("PDD_FORCE", "1")
    with patch("pdd.codex_subscription.bridge_codex_auth_for_litellm", return_value=False):
        assert li._ensure_api_key(_chatgpt_row(), {}, False) is False


def test_ensure_api_key_chatgpt_allowed_interactively_without_auth(monkeypatch):
    monkeypatch.delenv("PDD_FORCE", raising=False)
    for env_name in li._CLOUD_RUNTIME_ENV_KEYS:
        monkeypatch.delenv(env_name, raising=False)
    with patch("pdd.codex_subscription.bridge_codex_auth_for_litellm", return_value=False):
        # Interactive: allow litellm to attempt its own device-flow login.
        assert li._ensure_api_key(_chatgpt_row(), {}, False) is True


# --------------------------------------------------------------------------- #
# Reachability: ANTHROPIC unavailable -> candidate loop reaches chatgpt row
# --------------------------------------------------------------------------- #

def _fake_model_df():
    """Mimic _load_model_data output: an Anthropic row + the chatgpt row."""
    rows = [
        {
            "provider": "Anthropic", "model": "claude-sonnet-4-6",
            "input": 3.0, "output": 15.0, "coding_arena_elo": 1525,
            "base_url": "", "api_key": "ANTHROPIC_API_KEY",
            "max_reasoning_tokens": 0, "structured_output": True,
            "reasoning_type": "none", "location": "",
        },
        {
            "provider": "OpenAI ChatGPT", "model": "chatgpt/gpt-5.3-codex",
            "input": 0.0, "output": 0.0, "coding_arena_elo": 1407,
            "base_url": "", "api_key": "",
            "max_reasoning_tokens": 0, "structured_output": True,
            "reasoning_type": "none", "location": "",
        },
    ]
    df = pd.DataFrame(rows)
    df["avg_cost"] = (df["input"] + df["output"]) / 2
    df["structured_output"] = df["structured_output"].astype(bool)
    return df


def test_chatgpt_row_present_in_candidates():
    cands = li._select_model_candidates(0.5, "claude-sonnet-4-6", _fake_model_df())
    models = [c["model"] for c in cands]
    assert "chatgpt/gpt-5.3-codex" in models


def test_fallback_reaches_chatgpt_when_anthropic_key_missing(monkeypatch):
    """The load-bearing test: no ANTHROPIC_API_KEY, --force -> chatgpt is invoked."""
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
    monkeypatch.delenv("PDD_LLM_INVOKE_ANTHROPIC_API_KEY", raising=False)
    monkeypatch.setenv("PDD_FORCE", "1")
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")

    captured = {}

    def fake_completion(**kwargs):
        captured["model"] = kwargs.get("model")
        raise RuntimeError("STOP_AFTER_CAPTURE")

    with patch("pdd.llm_invoke._load_model_data", return_value=_fake_model_df()), \
         patch("pdd.codex_subscription.has_codex_subscription_auth", return_value=True), \
         patch("pdd.codex_subscription.bridge_codex_auth_for_litellm", return_value=True), \
         patch("pdd.llm_invoke.litellm.completion", side_effect=fake_completion):
        try:
            li.llm_invoke(prompt="hi {x}", input_json={"x": "there"}, strength=0.5, verbose=False)
        except Exception:
            pass

    # Anthropic row is skipped (missing key in --force); chatgpt is the first
    # model that actually reaches litellm.completion.
    assert captured.get("model") == "chatgpt/gpt-5.3-codex"


# --------------------------------------------------------------------------- #
# Codex subscription FAMILY (first-class provider, like Anthropic) — issue #1269
# --------------------------------------------------------------------------- #

def _packaged_model_df():
    """Load the bundled llm_model.csv exactly as llm_invoke does at runtime."""
    import importlib.resources
    import io as _io
    csv_text = importlib.resources.files("pdd").joinpath("data/llm_model.csv").read_text()
    return li._load_model_data.__wrapped__(None) if hasattr(li._load_model_data, "__wrapped__") else li._load_model_data(_packaged_csv_path())


def _packaged_csv_path():
    import importlib.resources
    from pathlib import Path as _P
    return _P(str(importlib.resources.files("pdd").joinpath("data/llm_model.csv")))


def test_codex_family_present_in_packaged_csv():
    """The subscription family the user's plan serves, with raw ELO plus rank score."""
    df = li._load_model_data(_packaged_csv_path())
    fam = df[df["provider"] == "OpenAI ChatGPT"]
    by_model = {r["model"]: r for _, r in fam.iterrows()}
    expected = {
        "chatgpt/gpt-5.6": (0, 17001),
        "chatgpt/gpt-5.5": (1450, 17000),
        "chatgpt/gpt-5.4": (1437, 15600),
        "chatgpt/gpt-5.3-codex": 1407,
        "chatgpt/gpt-5.2": 1404,
        "chatgpt/gpt-5.3-codex-spark": 1400,
    }
    assert set(by_model) == set(expected), f"family mismatch: {sorted(by_model)}"
    for model, expected_value in expected.items():
        elo = expected_value[0] if isinstance(expected_value, tuple) else expected_value
        assert int(by_model[model]["coding_arena_elo"]) == elo
        if isinstance(expected_value, tuple):
            assert int(by_model[model]["model_rank_score"]) == expected_value[1]
        # subscription rows carry NO api_key (device-flow / codex login)
        assert str(by_model[model]["api_key"] or "") == ""


def test_chatgpt_and_openai_api_models_do_not_collide():
    """Bare gpt-5.4 (OpenAI API key) and chatgpt/gpt-5.4 (subscription) must stay
    distinct rows under distinct providers — litellm routes on the chatgpt/ prefix,
    and the surrogate-base lookup must never collapse one into the other."""
    df = li._load_model_data(_packaged_csv_path())
    api = df[df["model"] == "gpt-5.4"]
    sub = df[df["model"] == "chatgpt/gpt-5.4"]
    assert not api.empty and not sub.empty
    assert api.iloc[0]["provider"] == "OpenAI"
    assert sub.iloc[0]["provider"] == "OpenAI ChatGPT"
    # the API row requires a key; the subscription row does not
    assert api.iloc[0]["api_key"] == "OPENAI_API_KEY"
    assert str(sub.iloc[0]["api_key"] or "") == ""


def test_codex_family_strength_orders_by_model_rank_score(monkeypatch):
    """Within the Codex family, high strength selects the GPT-5.6 platform default.

    Issue #1164: chatgpt/* rows are now ``interactive_only`` (device-flow / codex
    login), so the automatic candidate cascade skips the whole family by default
    — only the explicitly configured base would survive, collapsing this ranking.
    Intra-family ranking is therefore an opt-in scenario: set PDD_ALLOW_INTERACTIVE
    so the family is included, then assert the DeepSWE-weighted ranking."""
    monkeypatch.setenv("PDD_ALLOW_INTERACTIVE", "1")
    df = li._load_model_data(_packaged_csv_path())
    fam = df[df["provider"] == "OpenAI ChatGPT"].copy()
    cands = li._select_model_candidates(1.0, "chatgpt/gpt-5.3-codex", fam)
    assert cands[0]["model"] == "chatgpt/gpt-5.6", [c["model"] for c in cands]


def test_anthropic_outranks_codex_so_default_unchanged():
    """Promise to the user: Codex is opt-in, Anthropic stays the shipped default.
    Guard it numerically so a future ELO bump to a codex row can't silently steal
    the default-to-keep (which setup picks by highest ELO)."""
    df = li._load_model_data(_packaged_csv_path())
    amax = df[df["provider"] == "Anthropic"]["coding_arena_elo"].max()
    cmax = df[df["provider"] == "OpenAI ChatGPT"]["coding_arena_elo"].max()
    assert amax > cmax, f"Anthropic max {amax} must exceed Codex max {cmax}"


def test_chatgpt_structured_never_sends_response_format(monkeypatch):
    """P1b (#1269, Greg review): EVERY chatgpt/ structured completion attempt —
    the initial call AND the retry/repair calls — must (a) omit response_format
    (the subscription backend ignores it) and (b) carry the in-prompt schema
    instruction (the ONLY structured-output enforcement). Force non-JSON so the
    repair retry fires, then assert both invariants on every recorded call."""
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
    monkeypatch.setenv("PDD_FORCE", "1")
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    from pydantic import BaseModel

    class Cap(BaseModel):
        country: str
        capital: str

    df = pd.DataFrame([{
        "provider": "OpenAI ChatGPT", "model": "chatgpt/gpt-5.3-codex",
        "input": 0.0, "output": 0.0, "coding_arena_elo": 1407, "base_url": "",
        "api_key": "", "max_reasoning_tokens": 0, "structured_output": True,
        "reasoning_type": "none", "location": "",
    }])
    df["avg_cost"] = 0.0
    df["structured_output"] = df["structured_output"].astype(bool)

    # Marker from build_chatgpt_schema_instruction().
    SCHEMA_MARKER = "valid JSON object matching this schema"
    seen = []  # one entry per attempt: {"rf": bool, "schema": bool}

    def fake_completion(**kwargs):
        msgs = kwargs.get("messages") or []
        has_schema = any(
            isinstance(m, dict) and SCHEMA_MARKER in (m.get("content") or "")
            for m in msgs
        )
        seen.append({"rf": "response_format" in kwargs, "schema": has_schema})
        # Return None content to force the cache-bypass retry path (one of the
        # three retry sites), so we verify the retry call re-injects the schema.
        msg = type("M", (), {"content": None, "role": "assistant"})()
        choice = type("C", (), {"message": msg, "finish_reason": "stop"})()
        usage = type("U", (), {"prompt_tokens": 5, "completion_tokens": 5, "total_tokens": 10})()
        return type("R", (), {"choices": [choice], "usage": usage})()

    with patch("pdd.llm_invoke._load_model_data", return_value=df), \
         patch("pdd.codex_subscription.has_codex_subscription_auth", return_value=True), \
         patch("pdd.codex_subscription.bridge_codex_auth_for_litellm", return_value=True), \
         patch("pdd.codex_subscription.apply_litellm_chatgpt_output_patch", return_value=True), \
         patch("pdd.llm_invoke.litellm.completion", side_effect=fake_completion):
        try:
            li.llm_invoke(prompt="info about {c}", input_json={"c": "France"},
                          strength=0.5, output_pydantic=Cap, verbose=False)
        except Exception:
            pass

    assert seen, "litellm.completion was never called"
    assert len(seen) >= 2, f"expected initial + at least one retry attempt, got {seen}"
    assert not any(s["rf"] for s in seen), f"chatgpt/ call(s) sent response_format: {seen}"
    assert all(s["schema"] for s in seen), (
        f"a chatgpt/ structured attempt lacked the schema instruction (retry regressed): {seen}"
    )


def test_splice_collapses_gpt54_multi_message_output():
    """#1269 (Greg review): gpt-5.4 emits an empty phase='commentary' message plus
    the real phase='final_answer'; splice_codex_output_into_sse must collapse the
    empty response.completed.output to the single final_answer message (litellm's
    responses->chat transform mishandles multiple/empty message items)."""
    import json as _json
    from pdd.codex_subscription import splice_codex_output_into_sse

    def _data(obj):
        return "data: " + _json.dumps(obj)

    body = "\n".join([
        _data({"type": "response.created"}),
        _data({"type": "response.output_item.done", "item": {
            "type": "message", "phase": "commentary",
            "content": [{"type": "output_text", "text": ""}]}}),
        _data({"type": "response.output_item.done", "item": {
            "type": "message", "phase": "final_answer",
            "content": [{"type": "output_text", "text": "def add(a, b): return a + b"}]}}),
        _data({"type": "response.completed", "response": {"output": []}}),
        "data: [DONE]",
    ])

    out = splice_codex_output_into_sse(body)
    assert out is not None, "splice should rewrite the empty completed.output"

    completed = None
    for line in out.splitlines():
        s = line[len("data:"):].strip() if line.startswith("data:") else None
        if not s or s == "[DONE]":
            continue
        ev = _json.loads(s)
        if ev.get("type") == "response.completed":
            completed = ev
    assert completed is not None
    output = completed["response"]["output"]
    assert len(output) == 1, f"expected a single collapsed message, got {output}"
    assert output[0].get("phase") == "final_answer"
    text = "".join(p.get("text", "") for p in output[0].get("content", []))
    assert "def add" in text

    # No-op when the backend already populated completed.output.
    already = "\n".join([
        _data({"type": "response.output_item.done", "item": {
            "type": "message", "phase": "final_answer",
            "content": [{"type": "output_text", "text": "x"}]}}),
        _data({"type": "response.completed", "response": {"output": [{"type": "message"}]}}),
    ])
    assert splice_codex_output_into_sse(already) is None


def test_catalog_generator_preserves_chatgpt_family():
    """P1a: a catalog refresh must NOT drop the ChatGPT subscription rows. The
    generator skips chatgpt/* during litellm-derived generation, so it must
    re-merge the hand-managed family before returning."""
    import pdd.generate_model_catalog as gmc
    merged = gmc._merge_chatgpt_subscription_rows([{"model": "anthropic/claude", "provider": "Anthropic"}])
    cg = sorted(r["model"] for r in merged if str(r["model"]).startswith("chatgpt/"))
    assert cg == ["chatgpt/gpt-5.2", "chatgpt/gpt-5.3-codex",
                  "chatgpt/gpt-5.3-codex-spark", "chatgpt/gpt-5.4",
                  "chatgpt/gpt-5.5", "chatgpt/gpt-5.6"], cg
    again = gmc._merge_chatgpt_subscription_rows(merged)
    assert len([r for r in again if str(r["model"]).startswith("chatgpt/")]) == 6
    elos = {r["model"]: r["coding_arena_elo"] for r in again if str(r["model"]).startswith("chatgpt/")}
    assert elos["chatgpt/gpt-5.4"] == "1437"
    assert elos["chatgpt/gpt-5.5"] == "1450"
    assert elos["chatgpt/gpt-5.3-codex"] == "1407"


# --------------------------------------------------------------------------- #
# setup availability gate: chatgpt/ rows require real codex auth (#1269 review FM1)
# --------------------------------------------------------------------------- #

def test_empty_api_key_row_usable_gates_chatgpt_on_codex_auth(monkeypatch):
    """A chatgpt/ subscription row (empty api_key) is only 'usable' for setup
    default-keep / smoke-test when a real codex login exists. Other device-login
    rows (e.g. github_copilot) stay usable regardless."""
    import pdd.setup_tool as st

    chatgpt_row = {"provider": "OpenAI ChatGPT", "model": "chatgpt/gpt-5.4", "api_key": ""}
    copilot_row = {"provider": "Github Copilot", "model": "github_copilot/gpt-5", "api_key": ""}

    monkeypatch.setattr("pdd.codex_subscription.has_codex_subscription_auth", lambda: False)
    assert st._empty_api_key_row_usable(chatgpt_row) is False
    assert st._empty_api_key_row_usable(copilot_row) is True

    monkeypatch.setattr("pdd.codex_subscription.has_codex_subscription_auth", lambda: True)
    assert st._empty_api_key_row_usable(chatgpt_row) is True


# --------------------------------------------------------------------------- #
# Auth-state edge cases (review round 3, P1)
# --------------------------------------------------------------------------- #

def test_bridge_rejects_invalid_user_token_dir(tmp_path, monkeypatch):
    """P1a: a user CHATGPT_TOKEN_DIR holding a present-but-invalid auth.json must
    NOT be treated as usable — otherwise the --force credential gate is bypassed
    and litellm fails at call time. bridge() and has_auth() must agree (both False)."""
    bad = tmp_path / "userdir"
    bad.mkdir()
    (bad / "auth.json").write_text(json.dumps({"garbage": True}))  # no access_token
    monkeypatch.setenv("CHATGPT_TOKEN_DIR", str(bad))
    monkeypatch.setenv("CODEX_HOME", str(tmp_path / "empty-codex"))  # no source token
    monkeypatch.delenv("PDD_CHATGPT_TOKEN_DIR", raising=False)
    monkeypatch.delenv("CHATGPT_AUTH_FILE", raising=False)

    assert cs.bridge_codex_auth_for_litellm() is False
    assert cs.has_codex_subscription_auth() is False


def test_bridge_honors_chatgpt_auth_file_name(tmp_path, monkeypatch):
    """P1b: when CHATGPT_AUTH_FILE names a custom file, the bridge must stage the
    token under THAT name (litellm reads $CHATGPT_TOKEN_DIR/$CHATGPT_AUTH_FILE)."""
    codex_home = tmp_path / "codex"
    codex_home.mkdir()
    (codex_home / "auth.json").write_text(json.dumps(_nested_auth()))
    bridged = tmp_path / "bridged"
    monkeypatch.setenv("CODEX_HOME", str(codex_home))
    monkeypatch.setenv("PDD_CHATGPT_TOKEN_DIR", str(bridged))
    monkeypatch.setenv("CHATGPT_AUTH_FILE", "custom.json")
    monkeypatch.delenv("CHATGPT_TOKEN_DIR", raising=False)

    assert cs.bridge_codex_auth_for_litellm() is True
    assert (bridged / "custom.json").is_file()       # staged under the custom name
    assert not (bridged / "auth.json").is_file()      # not the default name
    assert os.environ["CHATGPT_TOKEN_DIR"] == str(bridged)


# --------------------------------------------------------------------------- #
# Auth-state consistency (review round 4, P1)
# --------------------------------------------------------------------------- #

def test_bridge_exports_token_dir_on_staged_copy_success(tmp_path, monkeypatch):
    """P1: when the codex source is unusable but a prior staged copy is valid,
    bridge() must still EXPORT CHATGPT_TOKEN_DIR — returning True without it
    leaves litellm unable to find the token (call-time failure)."""
    codex = tmp_path / "codex"; codex.mkdir()
    (codex / "auth.json").write_text(json.dumps({"garbage": True}))  # unusable source
    bridged = tmp_path / "bridged"; bridged.mkdir()
    (bridged / "auth.json").write_text(json.dumps(_nested_auth()))   # valid staged copy
    import os as _os
    _os.utime(bridged / "auth.json", (1, 1))  # older -> enters re-stage path
    monkeypatch.setenv("CODEX_HOME", str(codex))
    monkeypatch.setenv("PDD_CHATGPT_TOKEN_DIR", str(bridged))
    monkeypatch.delenv("CHATGPT_TOKEN_DIR", raising=False)
    monkeypatch.delenv("CHATGPT_AUTH_FILE", raising=False)

    assert cs.bridge_codex_auth_for_litellm() is True
    assert os.environ.get("CHATGPT_TOKEN_DIR") == str(bridged)


def test_has_auth_agrees_with_bridge_on_staged_copy(tmp_path, monkeypatch):
    """P1: has_codex_subscription_auth() must see a token staged in PDD's private
    bridge dir even when ~/.codex/auth.json is absent and CHATGPT_TOKEN_DIR is
    unset — otherwise setup/curation/smoke hide a subscription llm_invoke can use."""
    codex = tmp_path / "codex"; codex.mkdir()  # no auth.json -> no source
    bridged = tmp_path / "bridged"; bridged.mkdir()
    (bridged / "auth.json").write_text(json.dumps(_nested_auth()))
    monkeypatch.setenv("CODEX_HOME", str(codex))
    monkeypatch.setenv("PDD_CHATGPT_TOKEN_DIR", str(bridged))
    monkeypatch.delenv("CHATGPT_TOKEN_DIR", raising=False)
    monkeypatch.delenv("CHATGPT_AUTH_FILE", raising=False)

    # bridge treats the staged copy as usable...
    assert cs.bridge_codex_auth_for_litellm() is True
    # ...and detection must agree even after the exported env is cleared.
    monkeypatch.delenv("CHATGPT_TOKEN_DIR", raising=False)
    assert cs.has_codex_subscription_auth() is True
