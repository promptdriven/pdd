"""Shared helpers for mapping --time floats to provider reasoning effort.

Both the top-level CLI (which sets ``PDD_REASONING_EFFORT`` for provider
subprocesses) and ``llm_invoke`` (which forwards an effort string to
LiteLLM) need the same ``time -> {low, medium, high}`` mapping. Keeping
the thresholds in a single helper prevents silent drift between the two
call sites.
"""

from typing import Literal


EffortLevel = Literal["low", "medium", "high"]


def time_to_effort_level(time: float) -> EffortLevel:
    """Map a --time float in [0.0, 1.0] to a reasoning-effort level.

    Thresholds use strict ``>`` so 0.3 maps to ``"low"`` and 0.7 maps to
    ``"medium"`` — matching the pre-existing behavior in
    ``llm_invoke`` that this helper replaces.
    """
    if time > 0.7:
        return "high"
    if time > 0.3:
        return "medium"
    return "low"
