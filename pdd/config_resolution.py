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
import os

from . import DEFAULT_STRENGTH, DEFAULT_TEMPERATURE, DEFAULT_TIME

_COMPRESSION_KEYS = (
    "context_compression",
    "compress_examples",
    "compress_test_context",
    "compression_fallback",
)


def apply_compression_env(config: Dict[str, Any]) -> None:
    """Export resolved compression settings to os.environ for preprocess().

    Only keys present in ``config`` are updated so partial updates (e.g. from
    ``fix_error_loop``) do not clear unrelated compression env vars.
    """
    if "context_compression" in config:
        context_compression = config["context_compression"]
        if context_compression is not None and str(context_compression).lower() == "off":
            os.environ.pop("PDD_CONTEXT_COMPRESSION", None)
        elif context_compression is not None:
            os.environ["PDD_CONTEXT_COMPRESSION"] = str(context_compression)

    if "compress_examples" in config:
        if config["compress_examples"]:
            os.environ["PDD_COMPRESS_EXAMPLES"] = "1"
        else:
            os.environ.pop("PDD_COMPRESS_EXAMPLES", None)

    if "compress_test_context" in config:
        if config["compress_test_context"]:
            os.environ["PDD_COMPRESS_TEST_CONTEXT"] = "1"
        else:
            os.environ.pop("PDD_COMPRESS_TEST_CONTEXT", None)

    if "compression_fallback" in config and config["compression_fallback"] is not None:
        os.environ["PDD_COMPRESSION_FALLBACK"] = str(config["compression_fallback"])


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
        Dict with resolved values for strength, temperature, time, and compression flags
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

    effective_config = {
        "strength": resolve_value("strength", DEFAULT_STRENGTH),
        "temperature": resolve_value("temperature", DEFAULT_TEMPERATURE),
        "time": resolve_value("time", DEFAULT_TIME),
        "context_compression": resolve_value("context_compression", "off"),
        "compress_examples": resolve_value("compress_examples", False),
        "compress_test_context": resolve_value("compress_test_context", False),
        "compression_fallback": resolve_value("compression_fallback", "full"),
    }

    apply_compression_env(effective_config)

    return effective_config
