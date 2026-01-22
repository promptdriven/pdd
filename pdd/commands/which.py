"""
pdd which - print the resolved configuration values and the candidate search paths that PDD will consider when locating prompts / examples / tests / generated outputs.
"""

from __future__ import annotations

from typing import Any, Optional
import inspect
import os
from pathlib import Path

import click
import json

def _uniq_keep_order(items: list[str]) -> list[str]:
    seen: set[str] = set()
    out: list[str] = []
    for it in items:
        if not it:
            continue
        if it in seen:
            continue
        seen.add(it)
        out.append(it)
    return out


def _absify_candidates(base_dir: Path, values: list[str]) -> list[str]:
    """Turn possibly-relative paths into absolute strings; keep order; de-dupe."""
    out: list[str] = []
    for v in values:
        if not v:
            continue
        p = Path(v)
        if not p.is_absolute():
            p = (base_dir / p)
        try:
            p = p.resolve()
        except Exception:
            # If the path can't be resolved (e.g. missing parents), still stringify it.
            p = p.absolute()
        out.append(str(p))
    return _uniq_keep_order(out)


def _print_kv_rows(rows: list[tuple[str, str]], *, indent: str = "") -> None:
    """Print aligned `key : value` rows."""
    if not rows:
        return
    width = max(len(k) for k, _ in rows)
    for k, v in rows:
        click.echo(f"{indent}{k.ljust(width)} : {v}")

def _print_list_section(title: str, items: list[str]) -> None:
    """Print a titled list section."""
    click.echo(f"{title} :")
    for it in items:
        click.echo(f"  - {it}")

@click.command(name="which")
@click.option(
    "--context",
    "context_name",
    default=None,
    help="Context name to resolve (prints 'none' if not set / not found).",
)
@click.option(
    "--prompts-dir",
    default=None,
    help="Override the prompts directory (highest precedence).",
)
@click.option(
    "--prompt-path",
    default=None,
    help="Alias for --prompts-dir (kept for compatibility).",
)
@click.option(
    "--json",
    "as_json",
    is_flag=True,
    default=False,
    help="Output machine-readable JSON instead of the pretty human format.",
)
def which(
    context_name: Optional[str],
    prompts_dir: Optional[str],
    prompt_path: Optional[str],
    as_json: bool,
) -> None:
    """Print the resolved configuration variables PDD will use."""

    # Prefer using the canonical resolver so the output matches real behavior.
    # `resolve_effective_config` is responsible for:
    # - locating .pddrc
    # - selecting the active context
    # - applying precedence rules (CLI > env > .pddrc defaults)
    from pdd.construct_paths import resolve_effective_config  # local import to keep startup light

    cli_overrides: dict[str, Any] = {}
    if prompts_dir is not None:
        cli_overrides["prompts_dir"] = prompts_dir
    if prompt_path is not None:
        cli_overrides["prompt_path"] = prompt_path

    # Call resolver with best-effort kwargs based on its signature.
    sig = inspect.signature(resolve_effective_config)
    kwargs: dict[str, Any] = {}

    for name in sig.parameters.keys():
        # Context override
        if name in {"context", "context_name", "context_id", "context_override"}:
            kwargs[name] = context_name
        # CLI overrides mapping
        elif name in {"cli_overrides", "cli_config", "cli_options", "cli", "overrides", "command_options"}:
            kwargs[name] = cli_overrides
        # Some implementations may accept these directly
        elif name in {"prompts_dir", "prompt_dir", "prompt_path"}:
            if name == "prompt_path":
                kwargs[name] = cli_overrides.get("prompt_path")
            else:
                kwargs[name] = cli_overrides.get("prompts_dir")
        # Quiet flag to suppress debug output
        elif name == "quiet":
            kwargs[name] = True

    try:
        effective = resolve_effective_config(**kwargs)
    except TypeError:
        # Fall back to calling without kwargs if the resolver has a different interface.
        effective = resolve_effective_config()
    
    # Unpack the tuple returned by resolve_effective_config:
    # (context, pddrc_path, context_config, resolved_config, original_context_config)
    if isinstance(effective, tuple) and len(effective) == 5:
        selected_context, pddrc_path, _, resolved, _ = effective
        # Normalize context to string
        selected_context = selected_context or "none"
        # Convert Path to string if needed
        if isinstance(pddrc_path, Path):
            pddrc_path = str(pddrc_path)
    elif isinstance(effective, dict):
        # Fallback for unexpected dict return (shouldn't happen based on signature)
        selected_context = effective.get("context") or "none"
        pddrc_path = effective.get("pddrc_path")
        resolved = effective.get("resolved_config") or {}
        if isinstance(pddrc_path, Path):
            pddrc_path = str(pddrc_path)
    else:
        # Fallback for unexpected return type
        selected_context = "none"
        pddrc_path = None
        resolved = {}

    # Try to find pddrc_path in resolved config as fallback (shouldn't normally be needed)
    if not pddrc_path and isinstance(resolved, dict):
        for key in ("pddrc_path", "pddrc", "rc_path", "config_path"):
            val = resolved.get(key)
            if isinstance(val, Path):
                pddrc_path = str(val)
                break
            if isinstance(val, str) and val:
                pddrc_path = val
                break

    config_base = (Path(pddrc_path).parent if pddrc_path and pddrc_path != "none" else Path.cwd())

    def _deep_get_first(d: Any, keys: tuple[str, ...]) -> Any:
        """Best-effort lookup for common keys in a (possibly nested) resolved config."""
        if not isinstance(d, dict):
            return None
        for k in keys:
            if k in d and d.get(k) not in (None, ""):
                return d.get(k)
        # Search one level deeper (keeps behavior stable / not too expensive)
        for v in d.values():
            if isinstance(v, dict):
                found = _deep_get_first(v, keys)
                if found not in (None, ""):
                    return found
        return None

    # Match construct_paths precedence for locating prompts.
    env_prompt_path = os.environ.get("PDD_PROMPT_PATH")
    env_prompts_dir = os.environ.get("PDD_PROMPTS_DIR")

    def _get_resolved_path(*keys: str) -> Optional[str]:
        val = _deep_get_first(resolved, keys)
        if val in (None, ""):
            return None
        return str(val)

    # Prompts candidates
    prompts_candidates_raw: list[str] = []
    # CLI overrides (highest)
    prompts_candidates_raw.append(str(cli_overrides.get("prompts_dir") or ""))
    prompts_candidates_raw.append(str(cli_overrides.get("prompt_path") or ""))
    # Env
    prompts_candidates_raw.append(str(env_prompt_path or ""))
    prompts_candidates_raw.append(str(env_prompts_dir or ""))
    # .pddrc / resolved config (lowest among explicit settings)
    prompts_candidates_raw.append(str(_get_resolved_path("prompts_dir", "prompt_dir") or ""))
    prompts_candidates_raw.append(str(_get_resolved_path("prompt_path") or ""))

    # Conventional fallbacks construct_paths commonly implies
    # (relative to config_base)
    prompts_candidates_raw.append("prompts")

    prompts_search_paths = _absify_candidates(config_base, prompts_candidates_raw)

    # Examples / Tests / Generate candidates: use the same "resolved" value if present,
    # otherwise fall back to conventional defaults.
    examples_candidates_raw: list[str] = []
    tests_candidates_raw: list[str] = []
    generate_candidates_raw: list[str] = []

    # CLI overrides are not exposed for these in this command currently, but include env + resolved.
    examples_candidates_raw.append(str(os.environ.get("PDD_EXAMPLE_OUTPUT_PATH", "")))
    tests_candidates_raw.append(str(os.environ.get("PDD_TEST_OUTPUT_PATH", "")))
    generate_candidates_raw.append(str(os.environ.get("PDD_GENERATE_OUTPUT_PATH", "")))

    examples_candidates_raw.append(str(_get_resolved_path("example_output_path") or ""))
    tests_candidates_raw.append(str(_get_resolved_path("test_output_path") or ""))
    generate_candidates_raw.append(str(_get_resolved_path("generate_output_path") or ""))

    # Conventional defaults (relative)
    examples_candidates_raw.append("context")
    tests_candidates_raw.append("tests")
    generate_candidates_raw.append("pdd")

    examples_search_paths = _absify_candidates(config_base, examples_candidates_raw)
    tests_search_paths = _absify_candidates(config_base, tests_candidates_raw)
    generate_search_paths = _absify_candidates(config_base, generate_candidates_raw)

    # Flatten 1-level deep to keep output readable and stable.
    flat: dict[str, Any] = {}
    for k, v in resolved.items():
        if k in {"context", "context_name"}:
            continue
        if isinstance(v, dict):
            for kk, vv in v.items():
                flat[f"{k}.{kk}"] = vv
        else:
            flat[k] = v

    if as_json:
        payload = {
            "pddrc": pddrc_path or None,
            "context": selected_context,
            "config_base": str(config_base.resolve()),
            "search_paths": {
                "prompts": prompts_search_paths,
                "examples": examples_search_paths,
                "tests": tests_search_paths,
                "generate": generate_search_paths,
            },
            "effective_config": flat,
        }
        click.echo(json.dumps(payload, indent=2, sort_keys=True))
        return

    click.echo("Resolved")
    _print_kv_rows(
        [
            ("pddrc", pddrc_path or "none"),
            ("context", selected_context),
        ],
        indent="  ",
    )

    click.echo("")
    click.echo("Search locations")
    _print_kv_rows([("config_base", str(config_base.resolve()))], indent="  ")
    _print_list_section("  prompts.search_paths", prompts_search_paths)
    _print_list_section("  examples.search_paths", examples_search_paths)
    _print_list_section("  tests.search_paths", tests_search_paths)
    _print_list_section("  generate.search_paths", generate_search_paths)

    click.echo("")
    click.echo("Effective config")

    # Pretty-print as aligned key/value lines.
    items: list[tuple[str, str]] = []
    for k in sorted(flat.keys()):
        try:
            v = flat[k]
            # Keep strings unquoted; repr everything else for clarity/stability.
            if isinstance(v, str):
                v_str = v
            else:
                v_str = repr(v)
        except Exception:
            v_str = repr(flat.get(k))
        items.append((k, v_str))

    key_width = max((len(k) for k, _ in items), default=0)
    for k, v_str in items:
        click.echo(f"{k.ljust(key_width)} : {v_str}")