"""Planners that select and order checkup tools for a ``CheckupAgent`` session.

Two implementations are provided:

* ``DeterministicPlanner`` — always returns all tools in a fixed order; safe for
  CI and does not require an LLM credential.
* ``LLMPlanner`` — reads the prompt text and asks an LLM to suggest which tools
  matter most and why; falls back to ``DeterministicPlanner`` if the call fails.

Set ``PDD_ALLOW_INTERACTIVE=1`` or configure a model credential to enable LLM
planning in interactive terminals (see ``llm_model.csv`` for model selection).
"""

from __future__ import annotations

import logging
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable, Optional

from .checkup_tools import ALL_TOOL_NAMES

logger = logging.getLogger(__name__)

_DEFAULT_TOOL_ORDER = list(ALL_TOOL_NAMES)


@dataclass
class Plan:
    """Ordered list of tool names and the rationale behind the choice."""

    tools: list[str]
    rationale: str = ""

    def __post_init__(self) -> None:
        unknown = [t for t in self.tools if t not in ALL_TOOL_NAMES]
        if unknown:
            raise ValueError(f"Unknown tool(s) in plan: {unknown!r}. Valid: {ALL_TOOL_NAMES}")

    def display_lines(self) -> list[str]:
        lines = []
        for i, tool in enumerate(self.tools, 1):
            lines.append(f"  {i}. {tool}")
        if self.rationale:
            lines.append(f"  Rationale: {self.rationale}")
        return lines


class DeterministicPlanner:
    """Always selects all tools in the canonical order — no LLM call required."""

    def suggest(
        self,
        prompt_path: Path,  # noqa: ARG002
        available_tools: list[str],
        prompt_text: str = "",  # noqa: ARG002
    ) -> Plan:
        ordered = [t for t in _DEFAULT_TOOL_ORDER if t in available_tools]
        return Plan(
            tools=ordered,
            rationale="Run all checks in standard order.",
        )


_LLM_PLANNER_PROMPT = """\
You are a code-quality agent planning a checkup for a PDD (Prompt-Driven Development) prompt file.

Available checkup tools:
- lint: scan for vague language and ambiguous requirements
- contract: verify contract rules are well-formed and testable
- coverage: check that user stories are covered by contract rules
- gate: verify evidence manifests and waiver policy
- snapshot: ensure nondeterministic prompt context has a replayable snapshot
- drift: detect regeneration drift between prompt and generated output

Prompt content (first 3000 characters):
---
{prompt_excerpt}
---

Return a JSON object with:
- "tools": ordered list of tool names to run (subset of available tools, most important first)
- "rationale": one sentence explaining your prioritisation

Only include tools that are relevant given the prompt content.
Always include "lint" and "contract" if the prompt has requirements or rules.
Include "coverage" if user stories or acceptance tests are present.
Include "snapshot" only if <include query=...> or <shell> or <web> tags are present.
Include "drift" only if the prompt appears to be a devunit (has a generated output reference).
Include "gate" if the prompt references evidence or waivers.
"""


def _default_llm_call(
    prompt_excerpt: str,
    available_tools: list[str],
) -> dict:
    """Call llm_invoke and return parsed plan dict. Separated for testability."""
    from pydantic import BaseModel  # pylint: disable=import-outside-toplevel

    from .llm_invoke import llm_invoke  # pylint: disable=import-outside-toplevel

    class _PlanSchema(BaseModel):
        tools: list[str]
        rationale: str

    result = llm_invoke(
        messages=[
            {
                "role": "user",
                "content": _LLM_PLANNER_PROMPT.format(prompt_excerpt=prompt_excerpt[:3000]),
            }
        ],
        output_pydantic=_PlanSchema,
        strength=0.3,
        temperature=0.1,
        time=0.1,
    )
    raw: dict = result.get("result", {})
    # Validate tool names — drop any the LLM hallucinated.
    validated_tools = [t for t in raw.get("tools", []) if t in available_tools]
    return {"tools": validated_tools, "rationale": raw.get("rationale", "")}


class LLMPlanner:
    """Calls an LLM to select and prioritise checkup tools.

    Falls back to ``DeterministicPlanner`` when:
    - ``PDD_ALLOW_INTERACTIVE`` is not set and the model requires interactive auth
    - The LLM call raises any exception (logged at WARNING level)
    """

    def __init__(
        self,
        *,
        _call: Optional[Callable[[str, list[str]], dict]] = None,
    ) -> None:
        self._call = _call or _default_llm_call
        self._fallback = DeterministicPlanner()

    def suggest(
        self,
        prompt_path: Path,
        available_tools: list[str],
        prompt_text: str = "",
    ) -> Plan:
        if not prompt_text:
            try:
                prompt_text = prompt_path.read_text(encoding="utf-8")
            except OSError:
                logger.warning("LLMPlanner: could not read %s; falling back.", prompt_path)
                return self._fallback.suggest(prompt_path, available_tools, "")

        try:
            raw = self._call(prompt_text, available_tools)
        except Exception as exc:  # pylint: disable=broad-except
            logger.warning("LLMPlanner: LLM call failed (%s); falling back to deterministic.", exc)
            return self._fallback.suggest(prompt_path, available_tools, prompt_text)

        tools = raw.get("tools") or []
        if not tools:
            logger.warning("LLMPlanner: LLM returned empty tool list; falling back.")
            return self._fallback.suggest(prompt_path, available_tools, prompt_text)

        # Ensure all available tools are included — LLM might have under-selected.
        # Append any missing tools at the end so nothing is silently skipped.
        seen = set(tools)
        extras = [t for t in _DEFAULT_TOOL_ORDER if t in available_tools and t not in seen]
        return Plan(
            tools=tools + extras,
            rationale=raw.get("rationale", ""),
        )


PLANNERS: dict[str, type] = {
    "deterministic": DeterministicPlanner,
    "llm": LLMPlanner,
}


def make_planner(name: str) -> DeterministicPlanner | LLMPlanner:
    """Instantiate a planner by name. Raises ``ValueError`` for unknown names."""
    cls = PLANNERS.get(name)
    if cls is None:
        raise ValueError(f"Unknown planner {name!r}. Valid: {sorted(PLANNERS)}")
    return cls()
