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
    """Isolated CODEX_HOME + bridged dir; clears inherited CHATGPT_TOKEN_DIR / CODEX_API_KEY."""
    codex_home = tmp_path / "codex"
    codex_home.mkdir()
    bridged = tmp_path / "bridged"
    monkeypatch.setenv("CODEX_HOME", str(codex_home))
    monkeypatch.setenv("PDD_CHATGPT_TOKEN_DIR", str(bridged))
    monkeypatch.delenv("CHATGPT_TOKEN_DIR", raising=False)
    monkeypatch.delenv("CHATGPT_AUTH_FILE", raising=False)
    # CODEX_API_KEY is now a usable subscription signal (issue #1318); clear any
    # inherited value so detection/bridge tests start from a known-empty state.
    monkeypatch.delenv("CODEX_API_KEY", raising=False)
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


# --------------------------------------------------------------------------- #
# issue #1318 review FM3: CODEX_API_KEY is a usable subscription signal that the
# gate must accept AND the bridge must stage (else detection lies / route hangs).
# --------------------------------------------------------------------------- #

def test_has_codex_subscription_auth_accepts_codex_api_key(codex_env, monkeypatch):
    # No auth.json, but a token injected directly via CODEX_API_KEY (headless/CI).
    assert cs.has_codex_subscription_auth() is False
    monkeypatch.setenv("CODEX_API_KEY", "env-injected-token-XXXX")
    assert cs.has_codex_subscription_auth() is True


def test_bridge_stages_codex_api_key_token(codex_env, monkeypatch):
    # Gate-only would strand the call; the bridge must stage CODEX_API_KEY as the
    # access_token litellm's chatgpt/ provider actually reads.
    _, bridged = codex_env
    monkeypatch.setenv("CODEX_API_KEY", "env-injected-token-XXXX")
    assert cs.bridge_codex_auth_for_litellm() is True
    staged = json.loads((bridged / "auth.json").read_text())
    assert staged["access_token"] == "env-injected-token-XXXX"
    assert os.environ["CHATGPT_TOKEN_DIR"] == str(bridged)
    assert cs._token_dir_has_usable_auth(bridged) is True


def test_bridge_prefers_auth_json_over_codex_api_key(codex_env, monkeypatch):
    # A real (rotation-aware) auth.json wins when both are present.
    codex_home, bridged = codex_env
    (codex_home / "auth.json").write_text(json.dumps(_nested_auth(access="file-token-AAAA")))
    monkeypatch.setenv("CODEX_API_KEY", "env-token-should-lose")
    assert cs.bridge_codex_auth_for_litellm() is True
    staged = json.loads((bridged / "auth.json").read_text())
    assert staged["access_token"] == "file-token-AAAA"


def test_empty_codex_api_key_is_not_a_signal(codex_env, monkeypatch):
    # Whitespace-only / empty CODEX_API_KEY must NOT register as auth.
    monkeypatch.setenv("CODEX_API_KEY", "   ")
    assert cs.has_codex_subscription_auth() is False
    assert cs.bridge_codex_auth_for_litellm() is False


@pytest.mark.parametrize("auth_json_state", ["absent", "malformed_no_token", "invalid_json", "usable"])
def test_codex_api_key_keeps_gate_and_bridge_consistent(codex_env, monkeypatch, auth_json_state):
    """Issue #1318 review FM2: a set CODEX_API_KEY must keep detection and the
    bridge in lock-step — has()==bridge()==True regardless of the $CODEX_HOME/
    auth.json state. The round-1 gap returned has=True / bridge=False when a
    malformed auth.json coexisted with a valid env token, stranding the call.
    """
    codex_home, _ = codex_env
    auth = codex_home / "auth.json"
    if auth_json_state == "malformed_no_token":
        auth.write_text(json.dumps({"tokens": {"refresh_token": "r"}}))  # no access_token
    elif auth_json_state == "invalid_json":
        auth.write_text("{ this is not valid json")
    elif auth_json_state == "usable":
        auth.write_text(json.dumps(_nested_auth(access="file-token-AAAA")))
    # "absent": leave no auth.json

    monkeypatch.setenv("CODEX_API_KEY", "env-injected-token-XXXX")
    assert cs.has_codex_subscription_auth() is True
    assert cs.bridge_codex_auth_for_litellm() is True  # never strands the chatgpt/ call
    # A usable token actually landed where litellm reads it.
    assert cs._token_dir_has_usable_auth(Path(os.environ["CHATGPT_TOKEN_DIR"])) is True


def test_bridge_fresh_codex_api_key_beats_stale_staged_copy(codex_env, monkeypatch):
    """Issue #1318 review FM2 (round 3): a freshly-rotated CODEX_API_KEY must be
    restaged over a stale prior-staged token when $CODEX_HOME/auth.json is
    unusable — the bridge must not silently keep serving the stale staged copy.
    """
    codex_home, bridged = codex_env
    # A stale token was staged by a prior run.
    bridged.mkdir(parents=True, exist_ok=True)
    (bridged / "auth.json").write_text(json.dumps({"access_token": "STALE-staged-token"}))
    # The codex auth.json is now malformed (e.g. a broken/rotated login).
    (codex_home / "auth.json").write_text("{ not valid json")
    # The caller injects a fresh rotated token via the env var.
    monkeypatch.setenv("CODEX_API_KEY", "FRESH-env-token-1234")

    assert cs.bridge_codex_auth_for_litellm() is True
    staged = json.loads((bridged / "auth.json").read_text())["access_token"]
    assert staged == "FRESH-env-token-1234"  # fresh env token wins, not the stale copy


def test_codex_default_does_not_hijack_explicit_nonopenai_provider(monkeypatch):
    # Even with Codex auth present (the "both Claude and Codex auth" machine in
    # the review), an explicit github_copilot/* pin must be left untouched.
    monkeypatch.setattr(
        "pdd.codex_subscription.has_codex_subscription_auth", lambda: True
    )
    df = pd.DataFrame([
        {"provider": "GitHub Copilot", "model": "github_copilot/gpt-5.3-codex",
         "api_key": "GITHUB_TOKEN", "coding_arena_elo": 1400},
        {"provider": "OpenAI ChatGPT", "model": "chatgpt/gpt-5.5",
         "api_key": "", "coding_arena_elo": 1500},
    ])
    out_df, resolved, used = li._apply_codex_subscription_default(
        df, "github_copilot/gpt-5.3-codex"
    )
    assert used is False
    assert resolved == "github_copilot/gpt-5.3-codex"
    # The explicit provider's row survives in the candidate universe.
    assert (out_df["model"] == "github_copilot/gpt-5.3-codex").any()


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
    return {"model": "chatgpt/gpt-5.5", "api_key": "", "provider": "OpenAI ChatGPT"}


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
    with patch("pdd.codex_subscription.bridge_codex_auth_for_litellm", return_value=False):
        # Interactive: allow litellm to attempt its own device-flow login.
        assert li._ensure_api_key(_chatgpt_row(), {}, False) is True


# --------------------------------------------------------------------------- #
# Reachability: ANTHROPIC unavailable -> candidate loop reaches chatgpt row
# --------------------------------------------------------------------------- #

def _fake_model_df():
    """Mimic _load_model_data output with Anthropic, Codex, and Gemini rows."""
    rows = [
        {
            "provider": "Anthropic", "model": "claude-sonnet-4-6",
            "input": 3.0, "output": 15.0, "coding_arena_elo": 1525,
            "base_url": "", "api_key": "ANTHROPIC_API_KEY",
            "max_reasoning_tokens": 0, "structured_output": True,
            "reasoning_type": "none", "location": "",
        },
        {
            "provider": "OpenAI ChatGPT", "model": "chatgpt/gpt-5.5",
            "input": 0.0, "output": 0.0, "coding_arena_elo": 1450,
            "base_url": "", "api_key": "",
            "max_reasoning_tokens": 0, "structured_output": True,
            "reasoning_type": "none", "location": "",
        },
        {
            "provider": "Google Vertex AI", "model": "vertex_ai/gemini-3-flash-preview",
            "input": 0.5, "output": 3.0, "coding_arena_elo": 1437,
            "base_url": "", "api_key": "GOOGLE_APPLICATION_CREDENTIALS|VERTEXAI_PROJECT|VERTEXAI_LOCATION",
            "max_reasoning_tokens": 0, "structured_output": True,
            "reasoning_type": "effort", "location": "global",
        },
    ]
    df = pd.DataFrame(rows)
    df["avg_cost"] = (df["input"] + df["output"]) / 2
    df["structured_output"] = df["structured_output"].astype(bool)
    return df


def test_chatgpt_row_present_in_candidates():
    cands = li._select_model_candidates(0.5, "claude-sonnet-4-6", _fake_model_df())
    models = [c["model"] for c in cands]
    assert "chatgpt/gpt-5.5" in models


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
         patch("pdd.codex_subscription.bridge_codex_auth_for_litellm", return_value=True), \
         patch("pdd.llm_invoke.litellm.completion", side_effect=fake_completion):
        try:
            li.llm_invoke(prompt="hi {x}", input_json={"x": "there"}, strength=0.5, verbose=False)
        except Exception:
            pass

    # Anthropic row is skipped (missing key in --force); chatgpt is the first
    # model that actually reaches litellm.completion.
    assert captured.get("model") == "chatgpt/gpt-5.5"


def test_default_codex_auth_uses_chatgpt_even_when_anthropic_key_present(monkeypatch):
    """Issue #1318: Codex subscription auth must prevent default Anthropic billing."""
    monkeypatch.setenv("ANTHROPIC_API_KEY", "sk-ant-should-not-be-used")
    monkeypatch.setenv("PDD_FORCE", "1")
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    # Pin an OpenAI/Codex default at CALL time so the subscription restriction
    # fires deterministically. A bare delenv is env-fragile: a CI/cloud box that
    # exported PDD_MODEL_DEFAULT (a non-OpenAI model) at import freezes it into
    # DEFAULT_BASE_MODEL, which delenv can't undo — then no restriction fires and
    # claude (ANTHROPIC_API_KEY) wins by ELO (issue #1318 cloud-test).
    monkeypatch.setenv("PDD_MODEL_DEFAULT", "chatgpt/gpt-5.5")
    monkeypatch.setenv("PDD_MODEL_DEFAULT_FIRST", "1")

    captured = {}

    def fake_completion(**kwargs):
        # Capture the FIRST model tried (chatgpt/gpt-5.5 when the subscription
        # default is preferred). Capturing the last is env-fragile: where
        # Vertex/Gemini creds exist the gemini fallback row is also a candidate
        # and is tried after chatgpt (issue #1318 cloud-test).
        captured.setdefault("model", kwargs.get("model"))
        raise RuntimeError("STOP_AFTER_CAPTURE")

    with patch("pdd.llm_invoke._load_model_data", return_value=_fake_model_df()), \
         patch("pdd.codex_subscription.has_codex_subscription_auth", return_value=True), \
         patch("pdd.codex_subscription.bridge_codex_auth_for_litellm", return_value=True), \
         patch("pdd.llm_invoke.litellm.completion", side_effect=fake_completion):
        try:
            li.llm_invoke(prompt="hi {x}", input_json={"x": "there"}, strength=1.0, verbose=False)
        except Exception:
            pass

    assert captured.get("model") == "chatgpt/gpt-5.5"  # chatgpt preferred (tried first)


def test_chatgpt_default_disables_cache_per_request_not_globally(monkeypatch):
    """Issue #1318 review FM3: a chatgpt/ call disables cache via a per-request
    cache={"no-cache": True} kwarg, NOT by mutating the process-global
    litellm.cache (which races with concurrent llm_invoke calls)."""
    monkeypatch.setenv("PDD_FORCE", "1")
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    # Pin an OpenAI/Codex default at call time (env-robust; see the note in
    # test_default_codex_auth_uses_chatgpt_even_when_anthropic_key_present).
    monkeypatch.setenv("PDD_MODEL_DEFAULT", "chatgpt/gpt-5.5")
    monkeypatch.setenv("PDD_MODEL_DEFAULT_FIRST", "1")

    sentinel = object()
    monkeypatch.setattr(li.litellm, "cache", sentinel, raising=False)
    captured = {}

    def fake_completion(**kwargs):
        # Capture the FIRST (chatgpt/) call's model + cache kwarg; the global is
        # checked on every call. Capturing the last model is env-fragile — a
        # Vertex gemini fallback row is also tried in cloud (issue #1318 cloud-test).
        if "model" not in captured:
            captured["model"] = kwargs.get("model")
            captured["cache_kwarg"] = kwargs.get("cache")
        captured["global_cache_during_call"] = li.litellm.cache
        raise RuntimeError("STOP_AFTER_CAPTURE")

    with patch("pdd.llm_invoke._load_model_data", return_value=_fake_model_df()), \
         patch("pdd.codex_subscription.has_codex_subscription_auth", return_value=True), \
         patch("pdd.codex_subscription.bridge_codex_auth_for_litellm", return_value=True), \
         patch("pdd.llm_invoke.litellm.completion", side_effect=fake_completion):
        try:
            li.llm_invoke(prompt="hi {x}", input_json={"x": "there"}, strength=1.0, verbose=False)
        except Exception:
            pass

    assert captured.get("model") == "chatgpt/gpt-5.5"
    assert captured.get("cache_kwarg") == {"no-cache": True}  # disabled per-request
    assert captured.get("global_cache_during_call") is sentinel  # never nulled globally
    assert li.litellm.cache is sentinel  # global untouched after the call


def test_provider_challenge_detection_scoped_to_chatgpt():
    """Issue #1318 review FM2: provider-challenge detection only fires for chatgpt/
    responses. Benign output from other providers that merely contains Cloudflare
    strings (e.g. generated Cloudflare-handling code/docs) must not be rejected."""
    benign = ('<div class="challenge-error-text">x</div> cf_chl_opt '
              '"Enable JavaScript and cookies to continue"')
    # Non-chatgpt providers: legitimate content, must NOT raise.
    for model in ("claude-sonnet-4-6", "gpt-5.5", "openai/gpt-5.4", "gemini/gemini-3-pro"):
        li._raise_if_provider_challenge_response(benign, model, 0)
    # chatgpt/: a real Cloudflare challenge still triggers fallback.
    with pytest.raises(li.SchemaValidationError):
        li._raise_if_provider_challenge_response(benign, "chatgpt/gpt-5.5", 0)


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
    """The subscription family the user's plan actually serves, ELO-mirrored to twins."""
    df = li._load_model_data(_packaged_csv_path())
    fam = df[df["provider"] == "OpenAI ChatGPT"]
    by_model = {r["model"]: r for _, r in fam.iterrows()}
    expected = {
        "chatgpt/gpt-5.5": 1450,
        "chatgpt/gpt-5.4": 1437,
        "chatgpt/gpt-5.3-codex": 1407,
        "chatgpt/gpt-5.2": 1404,
        "chatgpt/gpt-5.3-codex-spark": 1400,
    }
    assert set(by_model) == set(expected), f"family mismatch: {sorted(by_model)}"
    for model, elo in expected.items():
        assert int(by_model[model]["coding_arena_elo"]) == elo
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


def test_codex_family_strength_orders_by_elo(monkeypatch):
    """Within the Codex family, high strength selects the top-ELO model (gpt-5.5),
    mirroring Anthropic's haiku->opus spread. (Flat cost => ELO is the ordering key
    at strength>=0.5; same behavior as the GitHub Copilot family.)

    Issue #1164: chatgpt/* rows are now ``interactive_only`` (device-flow / codex
    login), so the automatic candidate cascade skips the whole family by default
    — only the explicitly configured base would survive, collapsing this ranking.
    Intra-family ranking is therefore an opt-in scenario: set PDD_ALLOW_INTERACTIVE
    so the family is included, then assert the ELO ordering."""
    monkeypatch.setenv("PDD_ALLOW_INTERACTIVE", "1")
    df = li._load_model_data(_packaged_csv_path())
    fam = df[df["provider"] == "OpenAI ChatGPT"].copy()
    cands = li._select_model_candidates(1.0, "chatgpt/gpt-5.3-codex", fam)
    assert cands[0]["model"] == "chatgpt/gpt-5.5", [c["model"] for c in cands]


def test_codex_subscription_does_not_capture_unset_public_default(monkeypatch):
    """Public llm_invoke does not force unset/default users onto chatgpt/*."""
    df = li._load_model_data(_packaged_csv_path())
    monkeypatch.delenv("PDD_MODEL_DEFAULT", raising=False)
    monkeypatch.setattr("pdd.codex_subscription.has_codex_subscription_auth", lambda: True)
    restricted, default_model, used = li._apply_codex_subscription_default(df, None)

    assert used is False
    assert default_model is None
    assert restricted is df


def test_codex_subscription_does_not_capture_bare_openai_default(monkeypatch):
    """Bare gpt-5.5 remains normal catalog/OpenAI selection in public pdd."""
    df = li._load_model_data(_packaged_csv_path())
    monkeypatch.setattr("pdd.codex_subscription.has_codex_subscription_auth", lambda: True)
    restricted, default_model, used = li._apply_codex_subscription_default(df, "gpt-5.5")

    assert used is False
    assert default_model == "gpt-5.5"
    assert restricted is df


def test_explicit_chatgpt_default_uses_subscription_family_with_normal_fallback(monkeypatch):
    """Apps/users opt in explicitly with PDD_MODEL_DEFAULT=chatgpt/..."""
    df = li._load_model_data(_packaged_csv_path())
    monkeypatch.setattr("pdd.codex_subscription.has_codex_subscription_auth", lambda: True)
    restricted, default_model, used = li._apply_codex_subscription_default(df, "chatgpt/gpt-5.5")

    assert used is True
    assert default_model == "chatgpt/gpt-5.5"
    assert "OpenAI ChatGPT" in set(restricted["provider"])
    assert any(restricted["api_key"].astype(str).str.contains("ANTHROPIC_API_KEY"))


def test_codex_subscription_uses_packaged_rows_when_active_catalog_is_stale(monkeypatch):
    """Cloud/user CSVs created before chatgpt rows should not block Codex sync."""
    active = pd.DataFrame(
        [
            {
                "provider": "Anthropic",
                "model": "claude-sonnet-4-6",
                "input": 3.0,
                "output": 15.0,
                "coding_arena_elo": 1525,
                "api_key": "ANTHROPIC_API_KEY",
                "structured_output": True,
                "reasoning_type": "budget",
            }
        ]
    )
    packaged = pd.DataFrame(
        [
            {
                "provider": "OpenAI ChatGPT",
                "model": "chatgpt/gpt-5.5",
                "input": 0.0,
                "output": 0.0,
                "coding_arena_elo": 1450,
                "api_key": "",
                "structured_output": True,
                "reasoning_type": "none",
            }
        ]
    )
    monkeypatch.setattr(li, "_load_model_data", lambda path: packaged)
    monkeypatch.setattr("pdd.codex_subscription.has_codex_subscription_auth", lambda: True)
    restricted, default_model, used = li._apply_codex_subscription_default(active, "chatgpt/gpt-5.5")

    assert used is True
    assert default_model == "chatgpt/gpt-5.5"
    assert restricted["model"].tolist() == ["chatgpt/gpt-5.5", "claude-sonnet-4-6"]


def test_codex_cloudflare_falls_back_to_vertex_gemini_not_anthropic(monkeypatch):
    """Cloudflare HTML from chatgpt/ must not strand sync or use Anthropic API key."""
    monkeypatch.setenv("PDD_FORCE", "1")
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    monkeypatch.setenv("PDD_MODEL_DEFAULT", "chatgpt/gpt-5.5")
    monkeypatch.setenv("PDD_MODEL_DEFAULT_FIRST", "1")
    monkeypatch.setenv("GOOGLE_APPLICATION_CREDENTIALS", "/tmp/fake-adc.json")
    monkeypatch.setenv("VERTEXAI_PROJECT", "test-project")
    monkeypatch.setenv("VERTEXAI_LOCATION", "global")
    monkeypatch.setenv("ANTHROPIC_API_KEY", "sk-ant-should-not-be-used")

    calls = []

    def fake_completion(**kwargs):
        model = kwargs.get("model")
        calls.append(model)
        if str(model).startswith("chatgpt/"):
            msg = type("M", (), {
                "content": '<span id="challenge-error-text">Enable JavaScript and cookies to continue</span>',
                "role": "assistant",
            })()
        else:
            msg = type("M", (), {"content": '{"ok": true}', "role": "assistant"})()
        choice = type("C", (), {"message": msg, "finish_reason": "stop"})()
        usage = type("U", (), {"prompt_tokens": 5, "completion_tokens": 5, "total_tokens": 10})()
        return type("R", (), {"choices": [choice], "usage": usage})()

    with patch("pdd.llm_invoke._load_model_data", return_value=_fake_model_df()), \
         patch("pdd.codex_subscription.has_codex_subscription_auth", return_value=True), \
         patch("pdd.codex_subscription.bridge_codex_auth_for_litellm", return_value=True), \
         patch("pdd.codex_subscription.apply_litellm_chatgpt_output_patch", return_value=True), \
         patch("pdd.llm_invoke.count_tokens_for_messages", return_value=10), \
         patch("pdd.llm_invoke.get_context_limit", return_value=1_000_000), \
         patch("pdd.llm_invoke.litellm.completion", side_effect=fake_completion):
        result = li.llm_invoke(
            prompt="return json for {x}",
            input_json={"x": "smoke"},
            strength=0.5,
            output_schema={"type": "object", "properties": {"ok": {"type": "boolean"}}, "required": ["ok"]},
            verbose=False,
        )

    assert calls[0] == "chatgpt/gpt-5.5"
    assert "vertex_ai/gemini-3-flash-preview" in calls
    assert "claude-sonnet-4-6" not in calls
    assert result["model_name"] == "vertex_ai/gemini-3-flash-preview"


def test_codex_cloudflare_plain_text_generation_falls_back_to_vertex(monkeypatch):
    """The initial code-generation call is unstructured; challenge HTML must not be accepted."""
    monkeypatch.setenv("PDD_FORCE", "1")
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    monkeypatch.setenv("PDD_MODEL_DEFAULT", "chatgpt/gpt-5.5")
    monkeypatch.setenv("PDD_MODEL_DEFAULT_FIRST", "1")
    monkeypatch.setenv("GOOGLE_APPLICATION_CREDENTIALS", "/tmp/fake-adc.json")
    monkeypatch.setenv("VERTEXAI_PROJECT", "test-project")
    monkeypatch.setenv("VERTEXAI_LOCATION", "global")
    monkeypatch.setenv("ANTHROPIC_API_KEY", "sk-ant-should-not-be-used")

    calls = []

    def fake_completion(**kwargs):
        model = kwargs.get("model")
        calls.append(model)
        if str(model).startswith("chatgpt/"):
            content = '<span id="challenge-error-text">Enable JavaScript and cookies to continue</span>'
        else:
            content = "def comment_line(line: str) -> str:\n    return '# ' + line"
        msg = type("M", (), {"content": content, "role": "assistant"})()
        choice = type("C", (), {"message": msg, "finish_reason": "stop"})()
        usage = type("U", (), {"prompt_tokens": 5, "completion_tokens": 5, "total_tokens": 10})()
        return type("R", (), {"choices": [choice], "usage": usage})()

    with patch("pdd.llm_invoke._load_model_data", return_value=_fake_model_df()), \
         patch("pdd.codex_subscription.has_codex_subscription_auth", return_value=True), \
         patch("pdd.codex_subscription.bridge_codex_auth_for_litellm", return_value=True), \
         patch("pdd.codex_subscription.apply_litellm_chatgpt_output_patch", return_value=True), \
         patch("pdd.llm_invoke.count_tokens_for_messages", return_value=10), \
         patch("pdd.llm_invoke.get_context_limit", return_value=1_000_000), \
         patch("pdd.llm_invoke.litellm.completion", side_effect=fake_completion):
        result = li.llm_invoke(
            prompt="write code for {x}",
            input_json={"x": "comment_line"},
            strength=0.5,
            verbose=False,
        )

    assert calls[0] == "chatgpt/gpt-5.5"
    assert "vertex_ai/gemini-3-flash-preview" in calls
    assert "claude-sonnet-4-6" not in calls
    assert "challenge-error-text" not in result["result"]
    assert result["model_name"] == "vertex_ai/gemini-3-flash-preview"


def test_codex_cloudflare_skips_remaining_chatgpt_family(monkeypatch):
    """After one chatgpt/ challenge, jump to Vertex instead of another chatgpt/ model."""
    monkeypatch.setenv("PDD_FORCE", "1")
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    monkeypatch.setenv("PDD_MODEL_DEFAULT", "chatgpt/gpt-5.5")
    monkeypatch.setenv("PDD_MODEL_DEFAULT_FIRST", "1")
    monkeypatch.setenv("GOOGLE_APPLICATION_CREDENTIALS", "/tmp/fake-adc.json")
    monkeypatch.setenv("VERTEXAI_PROJECT", "test-project")
    monkeypatch.setenv("VERTEXAI_LOCATION", "global")
    monkeypatch.setenv("ANTHROPIC_API_KEY", "sk-ant-should-not-be-used")

    df = _fake_model_df()
    df = pd.concat([
        df,
        pd.DataFrame([{
            "provider": "OpenAI ChatGPT", "model": "chatgpt/gpt-5.4",
            "input": 0.0, "output": 0.0, "coding_arena_elo": 1449,
            "base_url": "", "api_key": "",
            "max_reasoning_tokens": 0, "structured_output": True,
            "reasoning_type": "none", "location": "",
            "avg_cost": 0.0,
        }]),
    ], ignore_index=True)
    df["structured_output"] = df["structured_output"].astype(bool)

    calls = []

    def fake_completion(**kwargs):
        model = kwargs.get("model")
        calls.append(model)
        if str(model).startswith("chatgpt/"):
            content = '<span id="challenge-error-text">Enable JavaScript and cookies to continue</span>'
        else:
            content = "def comment_line(line: str) -> str:\n    return '# ' + line"
        msg = type("M", (), {"content": content, "role": "assistant"})()
        choice = type("C", (), {"message": msg, "finish_reason": "stop"})()
        usage = type("U", (), {"prompt_tokens": 5, "completion_tokens": 5, "total_tokens": 10})()
        return type("R", (), {"choices": [choice], "usage": usage})()

    with patch("pdd.llm_invoke._load_model_data", return_value=df), \
         patch("pdd.codex_subscription.has_codex_subscription_auth", return_value=True), \
         patch("pdd.codex_subscription.bridge_codex_auth_for_litellm", return_value=True), \
         patch("pdd.codex_subscription.apply_litellm_chatgpt_output_patch", return_value=True), \
         patch("pdd.llm_invoke.count_tokens_for_messages", return_value=10), \
         patch("pdd.llm_invoke.get_context_limit", return_value=1_000_000), \
         patch("pdd.llm_invoke.litellm.completion", side_effect=fake_completion):
        result = li.llm_invoke(
            prompt="write code for {x}",
            input_json={"x": "comment_line"},
            strength=0.5,
            verbose=False,
        )

    assert calls == ["chatgpt/gpt-5.5", "vertex_ai/gemini-3-flash-preview"]
    assert result["model_name"] == "vertex_ai/gemini-3-flash-preview"


def test_codex_cloudflare_cache_bypass_retry_falls_back_to_vertex(monkeypatch):
    """Challenge HTML from the cache-bypass retry must also trigger fallback."""
    monkeypatch.setenv("PDD_FORCE", "1")
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    monkeypatch.setenv("PDD_MODEL_DEFAULT", "chatgpt/gpt-5.5")
    monkeypatch.setenv("PDD_MODEL_DEFAULT_FIRST", "1")
    monkeypatch.setenv("GOOGLE_APPLICATION_CREDENTIALS", "/tmp/fake-adc.json")
    monkeypatch.setenv("VERTEXAI_PROJECT", "test-project")
    monkeypatch.setenv("VERTEXAI_LOCATION", "global")
    monkeypatch.setenv("ANTHROPIC_API_KEY", "sk-ant-should-not-be-used")

    calls = []

    def fake_completion(**kwargs):
        model = kwargs.get("model")
        calls.append(model)
        if str(model).startswith("chatgpt/") and calls.count(model) == 1:
            content = None
        elif str(model).startswith("chatgpt/"):
            content = '<span id="challenge-error-text">Enable JavaScript and cookies to continue</span>'
        else:
            content = "def comment_line(line: str) -> str:\n    return '# ' + line"
        msg = type("M", (), {"content": content, "role": "assistant"})()
        choice = type("C", (), {"message": msg, "finish_reason": "stop"})()
        usage = type("U", (), {"prompt_tokens": 5, "completion_tokens": 5, "total_tokens": 10})()
        return type("R", (), {"choices": [choice], "usage": usage})()

    with patch("pdd.llm_invoke._load_model_data", return_value=_fake_model_df()), \
         patch("pdd.codex_subscription.has_codex_subscription_auth", return_value=True), \
         patch("pdd.codex_subscription.bridge_codex_auth_for_litellm", return_value=True), \
         patch("pdd.codex_subscription.apply_litellm_chatgpt_output_patch", return_value=True), \
         patch("pdd.llm_invoke.count_tokens_for_messages", return_value=10), \
         patch("pdd.llm_invoke.get_context_limit", return_value=1_000_000), \
         patch("pdd.llm_invoke.litellm.completion", side_effect=fake_completion):
        result = li.llm_invoke(
            prompt="write code for {x}",
            input_json={"x": "comment_line"},
            strength=0.5,
            verbose=False,
        )

    assert calls[:2] == ["chatgpt/gpt-5.5", "chatgpt/gpt-5.5"]
    assert "vertex_ai/gemini-3-flash-preview" in calls
    assert "claude-sonnet-4-6" not in calls
    assert "challenge-error-text" not in result["result"]
    assert result["model_name"] == "vertex_ai/gemini-3-flash-preview"


def test_codex_cloudflare_cache_bypass_exception_falls_back_to_vertex(monkeypatch):
    """Challenge HTML raised by LiteLLM during retry must not become an ERROR string."""
    monkeypatch.setenv("PDD_FORCE", "1")
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    monkeypatch.setenv("PDD_MODEL_DEFAULT", "chatgpt/gpt-5.5")
    monkeypatch.setenv("PDD_MODEL_DEFAULT_FIRST", "1")
    monkeypatch.setenv("GOOGLE_APPLICATION_CREDENTIALS", "/tmp/fake-adc.json")
    monkeypatch.setenv("VERTEXAI_PROJECT", "test-project")
    monkeypatch.setenv("VERTEXAI_LOCATION", "global")
    monkeypatch.setenv("ANTHROPIC_API_KEY", "sk-ant-should-not-be-used")

    calls = []

    def fake_completion(**kwargs):
        model = kwargs.get("model")
        calls.append(model)
        if str(model).startswith("chatgpt/") and calls.count(model) == 1:
            content = None
        elif str(model).startswith("chatgpt/"):
            raise RuntimeError(
                '<span id="challenge-error-text">Enable JavaScript and cookies to continue</span>'
            )
        else:
            content = "def comment_line(line: str) -> str:\n    return '# ' + line"
        msg = type("M", (), {"content": content, "role": "assistant"})()
        choice = type("C", (), {"message": msg, "finish_reason": "stop"})()
        usage = type("U", (), {"prompt_tokens": 5, "completion_tokens": 5, "total_tokens": 10})()
        return type("R", (), {"choices": [choice], "usage": usage})()

    with patch("pdd.llm_invoke._load_model_data", return_value=_fake_model_df()), \
         patch("pdd.codex_subscription.has_codex_subscription_auth", return_value=True), \
         patch("pdd.codex_subscription.bridge_codex_auth_for_litellm", return_value=True), \
         patch("pdd.codex_subscription.apply_litellm_chatgpt_output_patch", return_value=True), \
         patch("pdd.llm_invoke.count_tokens_for_messages", return_value=10), \
         patch("pdd.llm_invoke.get_context_limit", return_value=1_000_000), \
         patch("pdd.llm_invoke.litellm.completion", side_effect=fake_completion):
        result = li.llm_invoke(
            prompt="write code for {x}",
            input_json={"x": "comment_line"},
            strength=0.5,
            verbose=False,
        )

    assert calls[:2] == ["chatgpt/gpt-5.5", "chatgpt/gpt-5.5"]
    assert "vertex_ai/gemini-3-flash-preview" in calls
    assert "claude-sonnet-4-6" not in calls
    assert "challenge-error-text" not in result["result"]
    assert result["model_name"] == "vertex_ai/gemini-3-flash-preview"


def test_codex_cloudflare_initial_exception_skips_chatgpt_family(monkeypatch):
    """Challenge HTML raised by the initial chatgpt call must jump to Vertex."""
    monkeypatch.setenv("PDD_FORCE", "1")
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    monkeypatch.setenv("PDD_MODEL_DEFAULT", "chatgpt/gpt-5.5")
    monkeypatch.setenv("PDD_MODEL_DEFAULT_FIRST", "1")
    monkeypatch.setenv("GOOGLE_APPLICATION_CREDENTIALS", "/tmp/fake-adc.json")
    monkeypatch.setenv("VERTEXAI_PROJECT", "test-project")
    monkeypatch.setenv("VERTEXAI_LOCATION", "global")
    monkeypatch.setenv("ANTHROPIC_API_KEY", "sk-ant-should-not-be-used")

    df = _fake_model_df()
    df = pd.concat([
        df,
        pd.DataFrame([{
            "provider": "OpenAI ChatGPT", "model": "chatgpt/gpt-5.4",
            "input": 0.0, "output": 0.0, "coding_arena_elo": 1449,
            "base_url": "", "api_key": "",
            "max_reasoning_tokens": 0, "structured_output": True,
            "reasoning_type": "none", "location": "",
            "avg_cost": 0.0,
        }]),
    ], ignore_index=True)
    df["structured_output"] = df["structured_output"].astype(bool)
    calls = []

    def fake_completion(**kwargs):
        model = kwargs.get("model")
        calls.append(model)
        if str(model).startswith("chatgpt/"):
            raise RuntimeError(
                '<span id="challenge-error-text">Enable JavaScript and cookies to continue</span>'
            )
        msg = type("M", (), {
            "content": "def comment_line(line: str) -> str:\n    return '# ' + line",
            "role": "assistant",
        })()
        choice = type("C", (), {"message": msg, "finish_reason": "stop"})()
        usage = type("U", (), {"prompt_tokens": 5, "completion_tokens": 5, "total_tokens": 10})()
        return type("R", (), {"choices": [choice], "usage": usage})()

    with patch("pdd.llm_invoke._load_model_data", return_value=df), \
         patch("pdd.codex_subscription.has_codex_subscription_auth", return_value=True), \
         patch("pdd.codex_subscription.bridge_codex_auth_for_litellm", return_value=True), \
         patch("pdd.codex_subscription.apply_litellm_chatgpt_output_patch", return_value=True), \
         patch("pdd.llm_invoke.count_tokens_for_messages", return_value=10), \
         patch("pdd.llm_invoke.get_context_limit", return_value=1_000_000), \
         patch("pdd.llm_invoke.litellm.completion", side_effect=fake_completion):
        result = li.llm_invoke(
            prompt="write code for {x}",
            input_json={"x": "comment_line"},
            strength=0.5,
            verbose=False,
        )

    assert calls == ["chatgpt/gpt-5.5", "vertex_ai/gemini-3-flash-preview"]
    assert result["model_name"] == "vertex_ai/gemini-3-flash-preview"


def test_codex_cloudflare_pydantic_content_falls_back_to_vertex(monkeypatch):
    """Challenge HTML inside a structured object must also trigger fallback."""
    from pdd.postprocess import ExtractedCode

    monkeypatch.setenv("PDD_FORCE", "1")
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    monkeypatch.setenv("PDD_MODEL_DEFAULT", "chatgpt/gpt-5.5")
    monkeypatch.setenv("PDD_MODEL_DEFAULT_FIRST", "1")
    monkeypatch.setenv("GOOGLE_APPLICATION_CREDENTIALS", "/tmp/fake-adc.json")
    monkeypatch.setenv("VERTEXAI_PROJECT", "test-project")
    monkeypatch.setenv("VERTEXAI_LOCATION", "global")
    monkeypatch.setenv("ANTHROPIC_API_KEY", "sk-ant-should-not-be-used")

    calls = []

    def fake_completion(**kwargs):
        model = kwargs.get("model")
        calls.append(model)
        if str(model).startswith("chatgpt/"):
            content = ExtractedCode(
                extracted_code=(
                    '<span id="challenge-error-text">'
                    "Enable JavaScript and cookies to continue</span>"
                )
            )
        else:
            content = ExtractedCode(
                extracted_code="def comment_line(line: str) -> str:\n    return '# ' + line"
            )
        msg = type("M", (), {"content": content, "role": "assistant"})()
        choice = type("C", (), {"message": msg, "finish_reason": "stop"})()
        usage = type("U", (), {"prompt_tokens": 5, "completion_tokens": 5, "total_tokens": 10})()
        return type("R", (), {"choices": [choice], "usage": usage})()

    with patch("pdd.llm_invoke._load_model_data", return_value=_fake_model_df()), \
         patch("pdd.codex_subscription.has_codex_subscription_auth", return_value=True), \
         patch("pdd.codex_subscription.bridge_codex_auth_for_litellm", return_value=True), \
         patch("pdd.codex_subscription.apply_litellm_chatgpt_output_patch", return_value=True), \
         patch("pdd.llm_invoke.count_tokens_for_messages", return_value=10), \
         patch("pdd.llm_invoke.get_context_limit", return_value=1_000_000), \
         patch("pdd.llm_invoke.litellm.completion", side_effect=fake_completion):
        result = li.llm_invoke(
            prompt="extract code for {x}",
            input_json={"x": "comment_line"},
            strength=0.5,
            output_pydantic=ExtractedCode,
            verbose=False,
        )

    assert calls[0] == "chatgpt/gpt-5.5"
    assert "vertex_ai/gemini-3-flash-preview" in calls
    assert "claude-sonnet-4-6" not in calls
    assert result["result"].extracted_code.startswith("def comment_line")
    assert result["model_name"] == "vertex_ai/gemini-3-flash-preview"


def test_pdd_model_default_first_pins_configured_default(monkeypatch):
    """PDD_MODEL_DEFAULT_FIRST keeps the configured default ahead of ELO interpolation."""
    monkeypatch.setenv("PDD_ALLOW_INTERACTIVE", "1")
    df = li._load_model_data(_packaged_csv_path())
    fam = df[df["provider"] == "OpenAI ChatGPT"].copy()
    candidates = li._select_model_candidates(1.0, "chatgpt/gpt-5.3-codex", fam)
    assert candidates[0]["model"] == "chatgpt/gpt-5.5"

    monkeypatch.setenv("PDD_MODEL_DEFAULT_FIRST", "1")
    default_name = "chatgpt/gpt-5.3-codex"
    candidates = li._pin_default_model_first(candidates, default_name)
    assert candidates[0]["model"] == default_name


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
    seen = []  # one entry per attempt: {"rf": bool, "schema": bool, "cache_disabled": bool}
    cache_marker = object()
    monkeypatch.setattr(li.litellm, "cache", cache_marker)

    def fake_completion(**kwargs):
        msgs = kwargs.get("messages") or []
        has_schema = any(
            isinstance(m, dict) and SCHEMA_MARKER in (m.get("content") or "")
            for m in msgs
        )
        seen.append({
            "rf": "response_format" in kwargs,
            "schema": has_schema,
            # FM3: cache is disabled per-request via cache={"no-cache": True},
            # NOT by mutating the process-global litellm.cache.
            "cache_disabled": kwargs.get("cache") == {"no-cache": True},
        })
        # Return None content to force the cache-bypass retry path (one of the
        # three retry sites), so we verify the retry call re-injects the schema.
        msg = type("M", (), {"content": None, "role": "assistant"})()
        choice = type("C", (), {"message": msg, "finish_reason": "stop"})()
        usage = type("U", (), {"prompt_tokens": 5, "completion_tokens": 5, "total_tokens": 10})()
        return type("R", (), {"choices": [choice], "usage": usage})()

    with patch("pdd.llm_invoke._load_model_data", return_value=df), \
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
    assert all(s["cache_disabled"] for s in seen), f"chatgpt/ call(s) used LiteLLM cache: {seen}"
    # FM3: the process-global litellm.cache must never be mutated (no concurrency race).
    assert li.litellm.cache is cache_marker


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
                  "chatgpt/gpt-5.5"], cg
    again = gmc._merge_chatgpt_subscription_rows(merged)
    assert len([r for r in again if str(r["model"]).startswith("chatgpt/")]) == 5
    elos = {r["model"]: r["coding_arena_elo"] for r in again if str(r["model"]).startswith("chatgpt/")}
    assert elos["chatgpt/gpt-5.5"] == "1450"
    assert elos["chatgpt/gpt-5.4"] == "1437"
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
