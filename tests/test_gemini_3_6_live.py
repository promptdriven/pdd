"""Credential-gated live acceptance tests for Gemini 3.6 Flash.

Run only against a non-production Vertex project:

    GOOGLE_CLOUD_PROJECT=... \
    PDD_RUN_REAL_LLM_TESTS=1 \
    PDD_MODEL_DEFAULT=vertex_ai/gemini-3.6-flash \
    pytest -m real tests/test_gemini_3_6_live.py -vv
"""

from __future__ import annotations

import importlib.util
import json
import os
import py_compile
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest


MODEL = "vertex_ai/gemini-3.6-flash"
ROLLBACK_MODEL = "vertex_ai/gemini-3.5-flash"
_LIVE_PROJECT = (
    os.getenv("VERTEXAI_PROJECT")
    or os.getenv("VERTEX_PROJECT")
    or os.getenv("GOOGLE_CLOUD_PROJECT")
    or os.getenv("GCP_PROJECT_ID")
)
_LIVE_CREDENTIALS = os.getenv("GOOGLE_APPLICATION_CREDENTIALS")

pytestmark = [
    pytest.mark.real,
    pytest.mark.skipif(
        os.getenv("PDD_RUN_REAL_LLM_TESTS") != "1",
        reason="Set PDD_RUN_REAL_LLM_TESTS=1 to run credentialed Gemini tests.",
    ),
]


@pytest.fixture(autouse=True)
def _restore_live_vertex_env(monkeypatch: pytest.MonkeyPatch) -> None:
    """Opt these gated tests back in after the suite clears provider credentials."""
    if os.getenv("PDD_RUN_REAL_LLM_TESTS") != "1":
        return
    if _LIVE_PROJECT:
        monkeypatch.setenv("GOOGLE_CLOUD_PROJECT", _LIVE_PROJECT)
        monkeypatch.setenv("VERTEXAI_PROJECT", _LIVE_PROJECT)
    if _LIVE_CREDENTIALS:
        monkeypatch.setenv("GOOGLE_APPLICATION_CREDENTIALS", _LIVE_CREDENTIALS)
    monkeypatch.setenv("VERTEXAI_LOCATION", "global")


def _project() -> str:
    project = (
        os.getenv("VERTEXAI_PROJECT")
        or os.getenv("VERTEX_PROJECT")
        or os.getenv("GOOGLE_CLOUD_PROJECT")
        or os.getenv("GCP_PROJECT_ID")
    )
    if not project:
        pytest.skip("Set GOOGLE_CLOUD_PROJECT or VERTEXAI_PROJECT.")
    if project == "prompt-driven-development":
        pytest.fail("Live acceptance tests must not run against the production project.")
    return project


def _assert_selected_model(result: dict[str, Any], expected: str = MODEL) -> None:
    assert result.get("model_name") == expected, result
    attempted = result.get("attempted_models") or []
    attempted_names = [
        item.get("model") if isinstance(item, dict) else item for item in attempted
    ]
    assert all(name in (None, expected) for name in attempted_names), attempted
    assert float(result.get("cost", 0.0)) >= 0.0


def test_live_vertex_single_structured_response() -> None:
    """The normal local llm_invoke path selects 3.6 and returns JSON."""
    project = _project()
    os.environ["GOOGLE_CLOUD_PROJECT"] = project
    os.environ["VERTEXAI_PROJECT"] = project
    os.environ["VERTEXAI_LOCATION"] = "global"
    os.environ["PDD_FORCE_LOCAL"] = "1"
    assert os.getenv("PDD_MODEL_DEFAULT") == MODEL

    from pdd.llm_invoke import llm_invoke

    result = llm_invoke(
        prompt='Return JSON with the single field "answer" set to "{value}".',
        input_json={"value": "OK"},
        strength=0.5,
        temperature=0.0,
        time=0.1,
        output_schema={
            "type": "object",
            "properties": {"answer": {"type": "string"}},
            "required": ["answer"],
            "additionalProperties": False,
        },
        use_cloud=False,
    )

    _assert_selected_model(result)
    payload = result["result"]
    if isinstance(payload, str):
        payload = json.loads(payload)
    assert payload["answer"] == "OK"


def test_live_vertex_batch_response() -> None:
    """The real batch path reaches Gemini 3.6 without sampling fields."""
    project = _project()
    os.environ["GOOGLE_CLOUD_PROJECT"] = project
    os.environ["VERTEXAI_PROJECT"] = project
    os.environ["VERTEXAI_LOCATION"] = "global"
    os.environ["PDD_FORCE_LOCAL"] = "1"
    assert os.getenv("PDD_MODEL_DEFAULT") == MODEL

    from pdd.llm_invoke import llm_invoke

    result = llm_invoke(
        prompt="Reply with only {value}.",
        input_json=[{"value": "ONE"}, {"value": "TWO"}],
        strength=0.5,
        temperature=0.0,
        time=0.1,
        use_batch_mode=True,
        use_cloud=False,
    )

    _assert_selected_model(result)
    responses = result["result"]
    assert isinstance(responses, list) and len(responses) == 2
    assert "ONE" in str(responses[0]).upper()
    assert "TWO" in str(responses[1]).upper()


def test_live_vertex_cache_bypass_boundary() -> None:
    """The shared retry boundary strips deprecated fields before a real call."""
    project = _project()

    from pdd import llm_invoke as llm_module

    kwargs: dict[str, Any] = {
        "model": MODEL,
        "messages": [{"role": "user", "content": "Reply with exactly OK."}],
        "temperature": 0.0,
        "top_p": 0.8,
        "top_k": 20,
        "max_tokens": 256,
        "vertex_project": project,
        "vertex_location": "global",
    }
    response = llm_module._completion_with_attribution(
        context={},
        attempt_id="gemini-3.6-live-retry",
        call_type="completion_retry_cache_bypass",
        model=MODEL,
        provider="google vertex ai",
        api_key_name="GOOGLE_APPLICATION_CREDENTIALS",
        kwargs=kwargs,
    )

    assert "temperature" not in kwargs
    assert "top_p" not in kwargs
    assert "top_k" not in kwargs
    assert response.choices[0].message.content.strip()


def test_live_cli_generate_and_rollback_smoke(tmp_path: Path) -> None:
    """Installed CLI generates runnable code, then the prior model still responds."""
    project = _project()
    prompt = tmp_path / "add_python.prompt"
    output = tmp_path / "add.py"
    prompt.write_text(
        "// Language: Python\n"
        "// Implement a function add(a, b) that returns a + b.\n"
        "// Output only runnable Python code.\n",
        encoding="utf-8",
    )
    env = os.environ.copy()
    env.update(
        {
            "GOOGLE_CLOUD_PROJECT": project,
            "VERTEXAI_PROJECT": project,
            "VERTEXAI_LOCATION": "global",
            "PDD_FORCE_LOCAL": "1",
            "PDD_MODEL_DEFAULT": MODEL,
            "PDD_AUTO_UPDATE": "false",
        }
    )
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "pdd",
            "--local",
            "--strength",
            "0.5",
            "--temperature",
            "0",
            "--time",
            "0.1",
            "generate",
            "--output",
            str(output),
            str(prompt),
        ],
        cwd=tmp_path,
        env=env,
        text=True,
        capture_output=True,
        timeout=600,
        check=False,
    )
    assert result.returncode == 0, f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
    assert output.exists(), result.stdout
    py_compile.compile(str(output), doraise=True)
    spec = importlib.util.spec_from_file_location("gemini_live_add", output)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    assert module.add(2, 3) == 5

    from pdd import llm_invoke as llm_module

    rollback_kwargs = {
        "model": ROLLBACK_MODEL,
        "messages": [{"role": "user", "content": "Reply with exactly OK."}],
        "temperature": 1.0,
        "max_tokens": 256,
        "vertex_project": project,
        "vertex_location": "global",
    }
    rollback = llm_module._completion_with_attribution(
        context={},
        attempt_id="gemini-3.5-rollback-live",
        call_type="completion_rollback_smoke",
        model=ROLLBACK_MODEL,
        provider="google vertex ai",
        api_key_name="GOOGLE_APPLICATION_CREDENTIALS",
        kwargs=rollback_kwargs,
    )
    assert rollback.choices[0].message.content.strip()
