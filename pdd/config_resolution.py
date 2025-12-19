"""
Centralized config resolution for all commands.

Single source of truth for resolving strength, temperature, and other config values.
This module ensures consistent priority ordering across all commands:
    1. CLI global options (--strength, --temperature) - highest priority
    2. pddrc context defaults - medium priority
    3. Hardcoded defaults - lowest priority
"""
from typing import Dict, Any, Optional
import click

from . import DEFAULT_STRENGTH, DEFAULT_TEMPERATURE, DEFAULT_TIME


def resolve_effective_config(
    ctx: click.Context,
    resolved_config: Dict[str, Any],
    param_overrides: Optional[Dict[str, Any]] = None
) -> Dict[str, Any]:
    """
    Resolve effective config values with proper priority.

    Priority (highest to lowest):
        1. Command parameter overrides (e.g., strength kwarg)
        2. CLI global options (--strength stored in ctx.obj)
        3. pddrc context defaults (from resolved_config)
        4. Hardcoded defaults

    Args:
        ctx: Click context with CLI options in ctx.obj
        resolved_config: Config returned by construct_paths (contains pddrc values)
        param_overrides: Optional command-specific parameter overrides

    Returns:
        Dict with resolved values for strength, temperature, time
    """
    ctx_obj = ctx.obj if ctx.obj else {}
    param_overrides = param_overrides or {}

    def resolve_value(key: str, default: Any) -> Any:
        # Priority 1: Command parameter override
        if key in param_overrides and param_overrides[key] is not None:
            return param_overrides[key]
        # Priority 2: CLI global option (only if key IS in ctx.obj - meaning CLI passed it)
        if key in ctx_obj:
            return ctx_obj[key]
        # Priority 3: pddrc context default
        if key in resolved_config and resolved_config[key] is not None:
            return resolved_config[key]
        # Priority 4: Hardcoded default
        return default

    return {
        "strength": resolve_value("strength", DEFAULT_STRENGTH),
        "temperature": resolve_value("temperature", DEFAULT_TEMPERATURE),
        "time": resolve_value("time", DEFAULT_TIME),
    }
