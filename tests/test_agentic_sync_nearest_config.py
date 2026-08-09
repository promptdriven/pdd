"""
Real-LLM regression tests for issue #1128: nearest-config-wins .pddrc resolution.

Verifies that `pdd/prompts/agentic_sync_python.prompt` specifies
nearest-config-wins resolution for `_resolve_module_cwd` (nested `.pddrc` takes
precedence over root `.pddrc`). If the spec ever regresses to the old
"root .pddrc is authoritative" behavior, an LLM reading the spec would answer
"project_root" and these tests would fail.

These tests ship alongside the prompt change in PR #1130 and serve as a
regression guard for the spec wording itself, not just the generated code.

Requires: PDD_RUN_REAL_LLM_TESTS=1 or PDD_RUN_ALL_TESTS=1
"""

import os
from pathlib import Path
from typing import Literal

import pytest
from pydantic import BaseModel, Field

from pdd.llm_invoke import llm_invoke

RUN_ALL_TESTS_ENABLED = os.getenv("PDD_RUN_ALL_TESTS") == "1"


def _skip_unless_real() -> None:
    """Skip unless real LLM tests are enabled."""
    if not (os.getenv("PDD_RUN_REAL_LLM_TESTS") or RUN_ALL_TESTS_ENABLED):
        pytest.skip(
            "Real LLM tests require API access; set "
            "PDD_RUN_REAL_LLM_TESTS=1 or PDD_RUN_ALL_TESTS=1."
        )


class ResolutionDecision(BaseModel):
    """Structured output for resolver behavior evaluation."""

    resolved_cwd: Literal["project_root", "nested_dir", "other"] = Field(
        description=(
            "The directory _resolve_module_cwd should return per the spec: "
            "'project_root' if it returns the project root, 'nested_dir' if "
            "it returns a nested subdirectory, 'other' if neither."
        )
    )
    reasoning: str = Field(description="Brief citation of the relevant spec rule.")


PROMPT_PATH = (
    Path(__file__).resolve().parent.parent
    / "pdd"
    / "prompts"
    / "agentic_sync_python.prompt"
)


def _load_spec() -> str:
    """Load the agentic_sync_python.prompt content."""
    return PROMPT_PATH.read_text()


def _evaluate_scenario(scenario: str) -> ResolutionDecision:
    """Ask an LLM to apply the spec to a scenario and return a structured decision."""
    spec = _load_spec()
    result = llm_invoke(
        messages=[
            {
                "role": "system",
                "content": (
                    "You are evaluating a Python spec for a function named "
                    "`_resolve_module_cwd`. Read the 'Dry-Run Validation' "
                    "section and the 'Helper Functions' entry for "
                    "`_resolve_module_cwd` in the provided spec. Apply the "
                    "rules literally to the given scenario. Respond with "
                    "resolved_cwd='project_root' if the function should "
                    "return the project root, 'nested_dir' if it should "
                    "return a nested subdirectory, or 'other' if neither. "
                    "Cite the specific rule from the spec in your reasoning. "
                    "Be strict and literal — do not invent behavior."
                ),
            },
            {
                "role": "user",
                "content": f"SPEC:\n{spec}\n\nSCENARIO:\n{scenario}",
            },
        ],
        output_pydantic=ResolutionDecision,
        strength=0.5,
        temperature=0.0,
        verbose=False,
    )
    return result["result"]


NESTED_WINS_SCENARIO = """\
A repo has two .pddrc files:
- project_root/.pddrc — context "extensions-github_pdd_app" with
  paths ["extensions/github_pdd_app/**"]
- project_root/extensions/github_pdd_app/.pddrc — context "services" with
  paths ["src/services/**"] and prompts_dir "prompts/src/services"

Call: _resolve_module_cwd("src/services/solving_orchestrator", project_root)

The nested .pddrc's "services" context specifically matches the basename
(via paths pattern "src/services/**"). The root .pddrc has no context
matching this basename. According to the spec, what should the function
return?
"""

CATCHALL_ROOT_SCENARIO = """\
A repo has two .pddrc files:
- project_root/.pddrc — context "default" with paths ["**"] (a pure catch-all)
- project_root/extensions/app/.pddrc — context "workers" with
  paths ["src/workers/pdd_executor/**"] and prompts_dir
  "prompts/src/workers/pdd_executor"

Call: _resolve_module_cwd("src/workers/pdd_executor/runner", project_root)

The nested .pddrc's "workers" context specifically matches the basename.
The root .pddrc is a catch-all "**" default context. According to the
spec, what should the function return?
"""


@pytest.mark.real
class TestResolverSpecNearestConfigWins:
    """Verify the prompt specifies nearest-config-wins resolution, not root-authoritative."""

    def test_nested_specific_match_returns_nested_dir(self) -> None:
        """With a specific nested match and a non-matching root, nested_dir wins.

        This scenario distinguishes the new spec from the old: under the
        previous "root .pddrc is authoritative" wording, the LLM would have
        answered 'project_root'. Under the current nearest-config-wins
        wording, the LLM should answer 'nested_dir'.
        """
        _skip_unless_real()

        decision = _evaluate_scenario(NESTED_WINS_SCENARIO)
        assert decision.resolved_cwd == "nested_dir", (
            f"Spec should resolve to nested_dir when a nested .pddrc "
            f"specifically matches the basename. Got: {decision.resolved_cwd}. "
            f"Reasoning: {decision.reasoning}"
        )

    def test_root_catchall_does_not_shadow_nested_specific(self) -> None:
        """A root catch-all `**` default must not shadow a nested specific match.

        This is the exact scenario from issue #1128: under the old spec, the
        root catch-all would cause `_resolve_module_cwd` to return
        project_root, making prompts in subdirectories invisible to sync.
        The fixed spec must specify nested_dir here.
        """
        _skip_unless_real()

        decision = _evaluate_scenario(CATCHALL_ROOT_SCENARIO)
        assert decision.resolved_cwd == "nested_dir", (
            f"Spec should not allow a root catch-all to shadow a nested "
            f"specific match. Got: {decision.resolved_cwd}. "
            f"Reasoning: {decision.reasoning}"
        )
