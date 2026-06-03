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

_CLI_COMPRESSION_OVERRIDE: Optional[Dict[str, Any]] = None


def set_cli_compression_override(cli_config: Optional[Dict[str, Any]]) -> None:
    """Remember explicit global CLI compression flags for later ``construct_paths`` calls."""
    global _CLI_COMPRESSION_OVERRIDE
    _CLI_COMPRESSION_OVERRIDE = dict(cli_config) if cli_config else None


def get_cli_compression_override() -> Optional[Dict[str, Any]]:
    """Return global CLI compression flags set at ``pdd`` entry, if any."""
    return _CLI_COMPRESSION_OVERRIDE


def _default_compression_config() -> Dict[str, Any]:
    return {
        "context_compression": None,
        "compress_examples": False,
        "compress_test_context": False,
        "compression_fallback": "full",
    }


def _compression_keys_from(config: Dict[str, Any]) -> Dict[str, Any]:
    """Extract compression settings from a config mapping with defaults."""
    effective = _default_compression_config()
    for key in _COMPRESSION_KEYS:
        if key in config and config[key] is not None:
            effective[key] = config[key]
    return effective


def _apply_compression_off_semantics(config: Dict[str, Any]) -> Dict[str, Any]:
    """Explicit ``context_compression=off`` disables all compression modes for debugging."""
    mode = config.get("context_compression")
    if mode is None or str(mode).lower() != "off":
        return config
    disabled = dict(config)
    disabled["context_compression"] = "off"
    disabled["compress_examples"] = False
    disabled["compress_test_context"] = False
    return disabled


def effective_compression_config(pddrc_config: Dict[str, Any]) -> Dict[str, Any]:
    """Merge ``.pddrc`` compression defaults with explicit global CLI overrides (CLI wins)."""
    effective = _compression_keys_from(pddrc_config)
    cli_override = get_cli_compression_override()
    if cli_override:
        for key, value in cli_override.items():
            if value is not None:
                effective[key] = value
    return _apply_compression_off_semantics(effective)


def apply_compression_env(config: Dict[str, Any]) -> None:
    """Export resolved compression settings to os.environ for preprocess().

    Only keys present in ``config`` are updated so partial updates (e.g. from
    ``fix_error_loop``) do not clear unrelated compression env vars unless
    ``context_compression`` is ``off``, which clears all compression env keys.
    """
    config = _apply_compression_off_semantics(dict(config))
    mode = config.get("context_compression") if "context_compression" in config else None
    compression_off = mode is not None and str(mode).lower() == "off"

    if compression_off:
        os.environ.pop("PDD_CONTEXT_COMPRESSION", None)
        os.environ.pop("PDD_COMPRESS_EXAMPLES", None)
        os.environ.pop("PDD_COMPRESS_TEST_CONTEXT", None)
    elif "context_compression" in config:
        if config["context_compression"] is None:
            os.environ.pop("PDD_CONTEXT_COMPRESSION", None)
        else:
            os.environ["PDD_CONTEXT_COMPRESSION"] = str(config["context_compression"])

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
        # Priority 2: CLI global option (only when explicitly set, not Click default None)
        if key in ctx_obj and ctx_obj[key] is not None:
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
        "context_compression": resolve_value("context_compression", None),
        "compress_examples": resolve_value("compress_examples", False),
        "compress_test_context": resolve_value("compress_test_context", False),
        "compression_fallback": resolve_value("compression_fallback", "full"),
    }
    effective_config = _apply_compression_off_semantics(effective_config)

    apply_compression_env(effective_config)

    return effective_config
