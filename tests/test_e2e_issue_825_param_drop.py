"""
E2E Test for Issue #825: pdd-change drops existing parameters when rewriting
architecture.json signatures.

This E2E test exercises the full sync path — from prompt files on disk through
parse_prompt_tags → update_architecture_from_prompt → architecture.json write —
verifying that existing function parameters are preserved when the prompt's
<pdd-interface> tag adds new parameters but omits pre-existing ones.

The bug: architecture_sync.py:416 does a full replacement
(module_entry['interface'] = tags['interface']) instead of merging, so any
parameter present in architecture.json but missing from the new tag is silently
dropped.

These tests FAIL on the buggy code and should PASS once the fix is applied.
"""

import json
import tempfile
from pathlib import Path

import pytest

from pdd.architecture_sync import (
    sync_all_prompts_to_architecture,
    update_architecture_from_prompt,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _make_project(tmp_path, arch_data, prompts):
    """Create a minimal project directory with architecture.json and prompt files.

    Args:
        tmp_path: pytest tmp_path fixture
        arch_data: list of dicts for architecture.json
        prompts: dict mapping filename -> content string

    Returns:
        (prompts_dir, architecture_path) as Path objects
    """
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    architecture_path = tmp_path / "architecture.json"
    architecture_path.write_text(
        json.dumps(arch_data, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    for filename, content in prompts.items():
        (prompts_dir / filename).write_text(content, encoding="utf-8")
    return prompts_dir, architecture_path


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

EXISTING_ARCH_ENTRY = {
    "filename": "orchestrator_python.prompt",
    "reason": "Orchestrates the agentic E2E fix workflow",
    "interface": {
        "type": "module",
        "module": {
            "functions": [
                {
                    "name": "run_agentic_e2e_fix_orchestrator",
                    "signature": "(issue_url, issue_content, repo_owner, repo_name, issue_number, issue_author, issue_title, cwd, verbose, quiet, use_github_state, protect_tests)",
                    "returns": "Tuple[bool, str, float, str, List[str]]",
                }
            ]
        },
    },
    "dependencies": ["llm_invoke_python.prompt"],
}

# Prompt with NEW params (ci_retries, skip_ci) but MISSING existing protect_tests
PROMPT_DROPS_PARAM = """\
<pdd-reason>Orchestrates the agentic E2E fix workflow</pdd-reason>

<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {
        "name": "run_agentic_e2e_fix_orchestrator",
        "signature": "(issue_url, issue_content, repo_owner, repo_name, issue_number, issue_author, issue_title, cwd, verbose, quiet, use_github_state, ci_retries=3, skip_ci=False)",
        "returns": "Tuple[bool, str, float, str, List[str]]"
      }
    ]
  }
}
</pdd-interface>

<pdd-dependency>llm_invoke_python.prompt</pdd-dependency>

% Orchestrator prompt content...
"""

# Prompt that correctly includes ALL params (existing + new)
PROMPT_PRESERVES_PARAM = """\
<pdd-reason>Orchestrates the agentic E2E fix workflow</pdd-reason>

<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {
        "name": "run_agentic_e2e_fix_orchestrator",
        "signature": "(issue_url, issue_content, repo_owner, repo_name, issue_number, issue_author, issue_title, cwd, verbose, quiet, use_github_state, protect_tests, ci_retries=3, skip_ci=False)",
        "returns": "Tuple[bool, str, float, str, List[str]]"
      }
    ]
  }
}
</pdd-interface>

<pdd-dependency>llm_invoke_python.prompt</pdd-dependency>

% Orchestrator prompt content...
"""


# ---------------------------------------------------------------------------
# E2E Tests
# ---------------------------------------------------------------------------

class TestIssue825E2EParameterDrop:
    """E2E tests for Issue #825: architecture.json must not silently drop
    existing function parameters during sync."""

    def test_e2e_sync_single_module_drops_protect_tests(self, tmp_path):
        """
        E2E reproduction of Issue #825: a single-module sync that adds
        ci_retries and skip_ci should NOT drop the pre-existing protect_tests
        parameter.

        This exercises the full path:
            prompt file on disk → parse_prompt_tags() →
            update_architecture_from_prompt() → architecture.json on disk

        Expected: protect_tests is preserved in the written architecture.json.
        Bug:      protect_tests is silently dropped.
        """
        prompts_dir, arch_path = _make_project(
            tmp_path,
            [EXISTING_ARCH_ENTRY],
            {"orchestrator_python.prompt": PROMPT_DROPS_PARAM},
        )

        result = update_architecture_from_prompt(
            "orchestrator_python.prompt",
            prompts_dir=prompts_dir,
            architecture_path=arch_path,
        )

        assert result["success"], f"Sync failed: {result.get('error')}"

        # Re-read architecture.json from disk to verify the written state
        written = json.loads(arch_path.read_text(encoding="utf-8"))
        written_sig = written[0]["interface"]["module"]["functions"][0]["signature"]

        assert "protect_tests" in written_sig, (
            f"BUG (Issue #825): protect_tests was silently dropped from "
            f"architecture.json during sync.\n"
            f"  Written signature: {written_sig}\n"
            f"  Expected: signature should contain protect_tests"
        )
        # Also verify the new params were added
        assert "ci_retries" in written_sig
        assert "skip_ci" in written_sig

    def test_e2e_sync_all_prompts_drops_protect_tests(self, tmp_path):
        """
        E2E test via sync_all_prompts_to_architecture (the batch entry point
        used by `pdd sync`).  Same scenario as above but through the higher-
        level API that iterates all modules.

        Expected: protect_tests preserved after full sync.
        Bug:      protect_tests dropped.
        """
        # Add a second module to ensure iteration works correctly
        second_entry = {
            "filename": "llm_invoke_python.prompt",
            "reason": "LLM invocation wrapper",
            "interface": {
                "type": "module",
                "module": {
                    "functions": [
                        {
                            "name": "llm_invoke",
                            "signature": "(prompt, model, temperature)",
                            "returns": "str",
                        }
                    ]
                },
            },
            "dependencies": [],
        }
        second_prompt = """\
<pdd-reason>LLM invocation wrapper</pdd-reason>

<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {
        "name": "llm_invoke",
        "signature": "(prompt, model, temperature)",
        "returns": "str"
      }
    ]
  }
}
</pdd-interface>

% LLM invoke prompt...
"""
        prompts_dir, arch_path = _make_project(
            tmp_path,
            [EXISTING_ARCH_ENTRY, second_entry],
            {
                "orchestrator_python.prompt": PROMPT_DROPS_PARAM,
                "llm_invoke_python.prompt": second_prompt,
            },
        )

        result = sync_all_prompts_to_architecture(
            prompts_dir=prompts_dir,
            architecture_path=arch_path,
        )

        assert result["success"], f"Sync failed: {result.get('errors')}"

        written = json.loads(arch_path.read_text(encoding="utf-8"))
        orch_sig = written[0]["interface"]["module"]["functions"][0]["signature"]

        assert "protect_tests" in orch_sig, (
            f"BUG (Issue #825): protect_tests silently dropped during "
            f"sync_all_prompts_to_architecture.\n"
            f"  Written signature: {orch_sig}"
        )
        assert "ci_retries" in orch_sig
        assert "skip_ci" in orch_sig

    def test_e2e_disk_state_roundtrip_preserves_params(self, tmp_path):
        """
        Full disk round-trip: write architecture.json + prompt, sync, then
        verify the on-disk architecture.json is a superset of the original.

        This simulates what happens after pdd-change modifies the prompt
        (adding new params) and the architecture sync runs automatically.
        """
        prompts_dir, arch_path = _make_project(
            tmp_path,
            [EXISTING_ARCH_ENTRY],
            {"orchestrator_python.prompt": PROMPT_DROPS_PARAM},
        )

        # Capture original params from the existing architecture entry
        original_sig = EXISTING_ARCH_ENTRY["interface"]["module"]["functions"][0]["signature"]
        # Extract param names (rough but sufficient for this test)
        original_params = {
            p.strip().split("=")[0]
            for p in original_sig.strip("()").split(",")
        }

        update_architecture_from_prompt(
            "orchestrator_python.prompt",
            prompts_dir=prompts_dir,
            architecture_path=arch_path,
        )

        written = json.loads(arch_path.read_text(encoding="utf-8"))
        written_sig = written[0]["interface"]["module"]["functions"][0]["signature"]
        written_params = {
            p.strip().split("=")[0]
            for p in written_sig.strip("()").split(",")
        }

        # The written params must be a SUPERSET of the originals
        dropped = original_params - written_params
        assert not dropped, (
            f"BUG (Issue #825): parameters dropped from architecture.json "
            f"during sync: {dropped}\n"
            f"  Original: {original_sig}\n"
            f"  Written:  {written_sig}"
        )

    def test_e2e_no_drop_when_prompt_has_all_params(self, tmp_path):
        """
        Positive control: when the prompt's interface tag includes ALL params
        (existing + new), no parameter should be dropped.

        This test should PASS on both buggy and fixed code.
        """
        prompts_dir, arch_path = _make_project(
            tmp_path,
            [EXISTING_ARCH_ENTRY],
            {"orchestrator_python.prompt": PROMPT_PRESERVES_PARAM},
        )

        update_architecture_from_prompt(
            "orchestrator_python.prompt",
            prompts_dir=prompts_dir,
            architecture_path=arch_path,
        )

        written = json.loads(arch_path.read_text(encoding="utf-8"))
        written_sig = written[0]["interface"]["module"]["functions"][0]["signature"]

        assert "protect_tests" in written_sig
        assert "ci_retries" in written_sig
        assert "skip_ci" in written_sig
