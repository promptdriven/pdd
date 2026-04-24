"""
Tests for issue #1272: pdd sync hangs indefinitely when cloud LLM endpoint stalls.

Root cause: 4 non-compliant cloud `requests.post` call sites either omit the
`timeout=` argument entirely or use hardcoded constants that ignore the
documented `PDD_CLOUD_TIMEOUT` environment variable.

Fix: All 4 sites must pass `timeout=get_cloud_request_timeout()` (the canonical
pattern already used by 8 sibling call sites).

Affected sites:
- pdd/sync_main.py:543       _auto_submit_example submitExample POST (no timeout)
- pdd/fix_main.py:538        auto_submit submitExample POST (no timeout)
- pdd/llm_invoke.py:411      _llm_invoke_cloud llmInvoke POST (hardcoded 300)
- pdd/fix_code_loop.py:154   cloud_crash_fix crashCode POST (hardcoded 400)

These tests invoke each caller with mocked dependencies and verify that
`requests.post` receives a non-trivial `timeout=` kwarg that respects
`PDD_CLOUD_TIMEOUT`. They FAIL on the current buggy code and PASS once each
call site is updated to the canonical pattern.
"""

from pathlib import Path
from unittest.mock import AsyncMock, MagicMock, mock_open, patch

import pytest
from click import Context

from pdd import DEFAULT_STRENGTH
from pdd.core.cloud import get_cloud_request_timeout


# ---------------------------------------------------------------------------
# Test 1: pdd/llm_invoke.py:411 — _llm_invoke_cloud should use the helper, not
# the hardcoded CLOUD_TIMEOUT = 300. Current buggy code passes `timeout=300`,
# which ignores PDD_CLOUD_TIMEOUT.
# ---------------------------------------------------------------------------
def test_llm_invoke_cloud_passes_timeout_from_helper(monkeypatch):
    """_llm_invoke_cloud must pass timeout=get_cloud_request_timeout() so that
    PDD_CLOUD_TIMEOUT is honored (currently hardcoded to 300 seconds).
    """
    # Choose a unique read-timeout value that cannot be confused with the
    # hardcoded 300 or default 900.
    monkeypatch.setenv("PDD_CLOUD_TIMEOUT", "137")

    with patch("pdd.core.cloud.CloudConfig") as mock_config, \
         patch("requests.post") as mock_post:
        mock_config.is_cloud_enabled.return_value = True
        mock_config.get_jwt_token.return_value = "fake_token"
        mock_config.get_endpoint_url.return_value = (
            "https://example.com/llmInvoke"
        )

        mock_response = MagicMock()
        mock_response.status_code = 200
        mock_response.json.return_value = {
            "result": "ok",
            "totalCost": 0.0,
            "modelName": "cloud-model",
        }
        mock_post.return_value = mock_response

        from pdd.llm_invoke import _llm_invoke_cloud

        _llm_invoke_cloud(
            prompt="Test",
            input_json={"topic": "x"},
            strength=0.5,
            temperature=0.1,
            verbose=False,
            output_pydantic=None,
            output_schema=None,
            time=0.25,
            use_batch_mode=False,
            messages=None,
            language=None,
        )

        mock_post.assert_called_once()
        kwargs = mock_post.call_args.kwargs
        assert "timeout" in kwargs, (
            "llm_invoke cloud POST must pass a `timeout=` kwarg to requests.post"
        )
        timeout_value = kwargs["timeout"]

        # Canonical pattern returns a (connect, read) tuple whose read element
        # reflects PDD_CLOUD_TIMEOUT. Accept either a tuple or a single int,
        # but it must honor the env var (not the hardcoded 300).
        if isinstance(timeout_value, tuple):
            assert timeout_value[1] == 137, (
                f"Read timeout should respect PDD_CLOUD_TIMEOUT=137, "
                f"got {timeout_value!r}"
            )
        else:
            assert timeout_value == 137, (
                f"Timeout should respect PDD_CLOUD_TIMEOUT=137, "
                f"got {timeout_value!r} (likely hardcoded 300)"
            )


# ---------------------------------------------------------------------------
# Test 2: pdd/sync_main.py:543 — _auto_submit_example submitExample POST has
# no `timeout=` argument at all. Process hangs indefinitely if the cloud
# stalls. This is the actual hang source reported in the issue.
# Scope addition: covers expansion item "pdd/sync_main.py:543 submitExample
# POST missing timeout argument (actual hang source for pdd sync)" identified
# by Step 6.
# ---------------------------------------------------------------------------
def test_sync_auto_submit_example_passes_timeout_kwarg(tmp_path, monkeypatch):
    """sync_main._auto_submit_example must pass timeout= to requests.post."""
    # Prepare minimal pdd_files
    prompt_path = tmp_path / "module_python.prompt"
    prompt_path.write_text("test prompt", encoding="utf-8")
    code_path = tmp_path / "module.py"
    code_path.write_text("print('hi')", encoding="utf-8")
    example_path = tmp_path / "example.py"  # not created
    test_path = tmp_path / "test_module.py"  # not created

    pdd_files = {
        "prompt": prompt_path,
        "code": code_path,
        "example": example_path,
        "test": test_path,
    }

    ctx = MagicMock(spec=Context)
    ctx.obj = {"quiet": True}

    monkeypatch.delenv("PDD_FORCE_LOCAL", raising=False)

    # preprocess, get_jwt_token, and requests are imported lazily inside
    # _auto_submit_example, so patch them at their source modules.
    # get_jwt_token is an `async def`; using AsyncMock here lets the real
    # `asyncio.run` await it without leaking an unawaited-coroutine warning.
    with patch("pdd.preprocess.preprocess", return_value="processed"), \
         patch("pdd.get_jwt_token.get_jwt_token", new_callable=AsyncMock,
               return_value="fake_jwt"), \
         patch("requests.post") as mock_post:

        mock_response = MagicMock()
        mock_response.status_code = 200
        mock_post.return_value = mock_response

        from pdd.sync_main import _auto_submit_example

        _auto_submit_example(
            basename="module",
            language="python",
            pdd_files=pdd_files,
            ctx=ctx,
        )

        mock_post.assert_called_once()
        kwargs = mock_post.call_args.kwargs
        assert "timeout" in kwargs, (
            "sync_main._auto_submit_example must pass timeout= to requests.post "
            "(this is the actual hang source for `pdd sync` — issue #1272)"
        )
        timeout_value = kwargs["timeout"]
        assert timeout_value is not None and timeout_value != 0, (
            f"timeout kwarg must be a non-trivial value, got {timeout_value!r}"
        )


# ---------------------------------------------------------------------------
# Test 3: pdd/fix_main.py:538 — auto_submit submitExample POST has no
# `timeout=` argument. Sibling copy-paste bug.
# Scope addition: covers expansion item "pdd/fix_main.py:538 submitExample POST
# missing timeout argument (sibling copy-paste bug)" identified by Step 6.
# ---------------------------------------------------------------------------
@pytest.fixture
def _fix_main_ctx():
    ctx = MagicMock(spec=Context)
    ctx.obj = {
        "force": False,
        "quiet": False,
        "strength": DEFAULT_STRENGTH,
        "temperature": 0.0,
        "verbose": False,
        "time": None,
        "context": None,
        "confirm_callback": None,
    }
    return ctx


@patch("pdd.fix_main.run_pytest_on_file")
@patch("pdd.fix_main.Path")
@patch("pdd.fix_main.construct_paths")
@patch("pdd.fix_main.fix_errors_from_unit_tests")
@patch("pdd.fix_main.CloudConfig.get_jwt_token", return_value=None)
@patch("pdd.fix_main.get_jwt_token", new_callable=AsyncMock)
def test_fix_main_auto_submit_passes_timeout_kwarg(
    mock_get_jwt_token,
    mock_cloud_jwt,
    mock_fix_errors,
    mock_construct_paths,
    mock_path,
    mock_run_pytest,
    _fix_main_ctx,
    monkeypatch,
):
    """fix_main's auto_submit submitExample POST must pass timeout="""
    from pdd.fix_main import fix_main

    # We need:
    #  - PDD_FORCE_LOCAL unset so auto_submit is reachable (it is gated at
    #    fix_main.py:443 with `not _env_flag_enabled("PDD_FORCE_LOCAL")`).
    #  - PDD_CLOUD_ONLY / PDD_NO_LOCAL_FALLBACK unset so cloud-fix auth
    #    failure silently falls back to local instead of raising UsageError.
    # Cloud auth is mocked to return None → cloud fix falls back, local fix
    # succeeds via `mock_fix_errors`, and the submitExample POST fires.
    monkeypatch.delenv("PDD_FORCE_LOCAL", raising=False)
    monkeypatch.delenv("PDD_CLOUD_ONLY", raising=False)
    monkeypatch.delenv("PDD_NO_LOCAL_FALLBACK", raising=False)

    mock_path.return_value.exists.return_value = True
    ctx = _fix_main_ctx
    ctx.obj["local"] = False
    mock_construct_paths.return_value = (
        {},
        {
            "prompt_file": "Test prompt content",
            "code_file": "Test code content",
            "unit_test_file": "Test test content",
            "error_file": "Error content",
        },
        {
            "output_test": "output/test_fixed.py",
            "output_code": "output/code_fixed.py",
            "output_results": "results/fix.log",
        },
        None,
    )
    mock_fix_errors.return_value = (
        True,
        True,
        "fixed test",
        "fixed code",
        "analysis",
        0.50,
        "gpt-4",
    )
    mock_run_pytest.return_value = (0, 0, 0, "All tests passed")
    mock_get_jwt_token.return_value = "fake_jwt_token"

    m_open = mock_open(read_data="verifier content")
    # `fix_main.get_language()` is called while building the auto_submit payload
    # (fix_main.py:487) and raises a RuntimeError when `PDD_PATH` is not set.
    # The test runs inside a fresh pytest process without that env var, so the
    # raise is caught by the submission try/except and `requests.post` is never
    # reached — producing a misleading "0 calls" failure. Stub it so the test
    # is hermetic and verifies only the timeout-kwarg contract.
    with patch("builtins.open", m_open), \
         patch("pdd.fix_main.preprocess", return_value="processed prompt"), \
         patch("pdd.fix_main.get_language", return_value="python"), \
         patch("pdd.fix_main.requests") as mock_requests:
        mock_response = MagicMock()
        mock_response.status_code = 200
        mock_requests.post.return_value = mock_response

        fix_main(
            ctx=ctx,
            prompt_file="prompt.prompt",
            code_file="code.py",
            unit_test_file="test.py",
            error_file="errors.log",
            output_test=None,
            output_code=None,
            output_results=None,
            loop=False,
            verification_program=None,
            max_attempts=3,
            budget=5.0,
            auto_submit=True,
        )

        mock_requests.post.assert_called_once()
        kwargs = mock_requests.post.call_args.kwargs
        assert "timeout" in kwargs, (
            "fix_main auto_submit submitExample POST must pass timeout= "
            "to requests.post (sibling of issue #1272 hang bug)"
        )
        timeout_value = kwargs["timeout"]
        assert timeout_value is not None and timeout_value != 0, (
            f"timeout kwarg must be a non-trivial value, got {timeout_value!r}"
        )


# ---------------------------------------------------------------------------
# Test 4: pdd/fix_code_loop.py:154 — cloud_crash_fix uses the module-level
# hardcoded CLOUD_REQUEST_TIMEOUT=400 constant, which ignores PDD_CLOUD_TIMEOUT.
# Scope addition: covers expansion item "pdd/fix_code_loop.py:154 uses
# hardcoded CLOUD_REQUEST_TIMEOUT=400 ignoring PDD_CLOUD_TIMEOUT env var"
# identified by Step 6.
# ---------------------------------------------------------------------------
def test_fix_code_loop_cloud_crash_fix_passes_timeout_from_helper(monkeypatch):
    """cloud_crash_fix must use get_cloud_request_timeout() so PDD_CLOUD_TIMEOUT
    is honored (currently hardcoded to 400 seconds).
    """
    monkeypatch.setenv("PDD_CLOUD_TIMEOUT", "251")

    with patch("pdd.fix_code_loop.CloudConfig") as mock_config, \
         patch("pdd.fix_code_loop.requests.post") as mock_post:
        mock_config.get_jwt_token.return_value = "fake_token"
        mock_config.get_endpoint_url.return_value = (
            "https://example.com/crashCode"
        )

        mock_response = MagicMock()
        mock_response.status_code = 200
        mock_response.raise_for_status.return_value = None
        mock_response.json.return_value = {
            "fixedCode": "code",
            "fixedProgram": "program",
            "updateCode": False,
            "updateProgram": False,
            "analysis": "",
            "totalCost": 0.0,
            "modelName": "m",
        }
        mock_post.return_value = mock_response

        from pdd.fix_code_loop import cloud_crash_fix

        cloud_crash_fix(
            program="p",
            prompt="prompt",
            code="code",
            errors="err",
            strength=0.5,
            temperature=0.0,
            time=0.25,
            verbose=False,
            program_path="prog.py",
            code_path="code.py",
            language="python",
        )

        mock_post.assert_called_once()
        kwargs = mock_post.call_args.kwargs
        assert "timeout" in kwargs, (
            "cloud_crash_fix must pass timeout= to requests.post"
        )
        timeout_value = kwargs["timeout"]

        if isinstance(timeout_value, tuple):
            assert timeout_value[1] == 251, (
                f"Read timeout should respect PDD_CLOUD_TIMEOUT=251, "
                f"got {timeout_value!r}"
            )
        else:
            assert timeout_value == 251, (
                f"Timeout should respect PDD_CLOUD_TIMEOUT=251, "
                f"got {timeout_value!r} (likely hardcoded 400)"
            )


# ---------------------------------------------------------------------------
# Test 5: Helper integration — get_cloud_request_timeout() returns a
# (connect, read) tuple where read honors PDD_CLOUD_TIMEOUT. When the canonical
# pattern is wired correctly in _llm_invoke_cloud, setting PDD_CLOUD_TIMEOUT
# must flow all the way to the mock requests.post call.
# ---------------------------------------------------------------------------
def test_llm_invoke_cloud_respects_pdd_cloud_timeout_env(monkeypatch):
    """Setting PDD_CLOUD_TIMEOUT must affect the timeout passed to
    requests.post in _llm_invoke_cloud (documented behavior per README).
    """
    monkeypatch.setenv("PDD_CLOUD_TIMEOUT", "42")

    expected = get_cloud_request_timeout()  # (connect, 42)
    assert expected[1] == 42, "helper should reflect env var"

    with patch("pdd.core.cloud.CloudConfig") as mock_config, \
         patch("requests.post") as mock_post:
        mock_config.is_cloud_enabled.return_value = True
        mock_config.get_jwt_token.return_value = "fake_token"
        mock_config.get_endpoint_url.return_value = (
            "https://example.com/llmInvoke"
        )

        mock_response = MagicMock()
        mock_response.status_code = 200
        mock_response.json.return_value = {
            "result": "ok",
            "totalCost": 0.0,
            "modelName": "m",
        }
        mock_post.return_value = mock_response

        from pdd.llm_invoke import _llm_invoke_cloud

        _llm_invoke_cloud(
            prompt="Test",
            input_json={"topic": "x"},
            strength=0.5,
            temperature=0.1,
            verbose=False,
            output_pydantic=None,
            output_schema=None,
            time=0.25,
            use_batch_mode=False,
            messages=None,
            language=None,
        )

        kwargs = mock_post.call_args.kwargs
        timeout_value = kwargs.get("timeout")

        # The hardcoded buggy value is 300, so 42 in the read slot proves the
        # fix is wired through the env var, not a hardcoded constant.
        read_timeout = (
            timeout_value[1] if isinstance(timeout_value, tuple) else timeout_value
        )
        assert read_timeout == 42, (
            f"PDD_CLOUD_TIMEOUT=42 must flow into requests.post timeout kwarg; "
            f"got {timeout_value!r}. On the current buggy code the hardcoded "
            f"300 seconds ignores the env var."
        )


# ---------------------------------------------------------------------------
# Test 6: Similarly, PDD_CLOUD_TIMEOUT must flow through cloud_crash_fix in
# fix_code_loop.py — currently it's hardcoded to 400, so the env var is
# ignored.
# ---------------------------------------------------------------------------
def test_fix_code_loop_respects_pdd_cloud_timeout_env(monkeypatch):
    """cloud_crash_fix must honor PDD_CLOUD_TIMEOUT (currently hardcoded 400)."""
    monkeypatch.setenv("PDD_CLOUD_TIMEOUT", "73")

    with patch("pdd.fix_code_loop.CloudConfig") as mock_config, \
         patch("pdd.fix_code_loop.requests.post") as mock_post:
        mock_config.get_jwt_token.return_value = "fake_token"
        mock_config.get_endpoint_url.return_value = (
            "https://example.com/crashCode"
        )

        mock_response = MagicMock()
        mock_response.status_code = 200
        mock_response.raise_for_status.return_value = None
        mock_response.json.return_value = {
            "fixedCode": "code",
            "fixedProgram": "program",
            "updateCode": False,
            "updateProgram": False,
            "analysis": "",
            "totalCost": 0.0,
            "modelName": "m",
        }
        mock_post.return_value = mock_response

        from pdd.fix_code_loop import cloud_crash_fix

        cloud_crash_fix(
            program="p",
            prompt="prompt",
            code="code",
            errors="err",
            strength=0.5,
            temperature=0.0,
            time=0.25,
            verbose=False,
        )

        kwargs = mock_post.call_args.kwargs
        timeout_value = kwargs.get("timeout")
        read_timeout = (
            timeout_value[1] if isinstance(timeout_value, tuple) else timeout_value
        )
        assert read_timeout == 73, (
            f"PDD_CLOUD_TIMEOUT=73 must flow into cloud_crash_fix's requests.post "
            f"timeout kwarg; got {timeout_value!r}. On the current buggy code "
            f"the hardcoded 400 seconds ignores the env var."
        )
