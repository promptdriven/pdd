"""`pdd config` command group — schema validation for .pddrc (Issue #1198).

This module exposes `pdd config validate`, a CI-friendly explicit checker for
the `.pddrc` configuration file. It walks the parsed YAML and reports any
keys not present in the canonical valid-key sets defined in
`pdd.construct_paths`. The same validation runs at load time inside
`_load_pddrc_config` (warn-not-fail); this command surfaces the check
explicitly with a non-zero exit code on any unknown key.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any, Dict, List, Tuple

import click
import yaml

from pdd.construct_paths import (
    _VALID_PDDRC_ROOT_KEYS,
    _VALID_CONTEXT_KEYS,
    _VALID_DEFAULTS_KEYS,
    _find_pddrc_file,
)


def _collect_pddrc_warnings(config: Dict[str, Any]) -> List[Tuple[str, str]]:
    """Return a list of (dotted_path, key) tuples for each unknown key found."""
    warnings: List[Tuple[str, str]] = []

    for root_key in config.keys():
        if root_key not in _VALID_PDDRC_ROOT_KEYS:
            warnings.append((root_key, root_key))

    contexts = config.get("contexts", {})
    if isinstance(contexts, dict):
        for ctx_name, ctx_val in contexts.items():
            if not isinstance(ctx_val, dict):
                continue
            for ctx_key in ctx_val.keys():
                if ctx_key not in _VALID_CONTEXT_KEYS:
                    warnings.append(
                        (f"contexts.{ctx_name}.{ctx_key}", ctx_key)
                    )
            defaults = ctx_val.get("defaults", {})
            if isinstance(defaults, dict):
                for def_key in defaults.keys():
                    if def_key not in _VALID_DEFAULTS_KEYS:
                        warnings.append(
                            (f"contexts.{ctx_name}.defaults.{def_key}", def_key)
                        )

    return warnings


@click.group(name="config")
def config_group() -> None:
    """Manage PDD configuration."""


@config_group.command("validate")
@click.option(
    "--file",
    "-f",
    "file_path",
    type=click.Path(dir_okay=False, path_type=Path),
    default=None,
    help="Path to a .pddrc file. Defaults to the nearest .pddrc.",
)
def validate(file_path: Path | None) -> None:
    """Validate a .pddrc file for unknown keys.

    Exits 0 when the config is schema-conformant, 1 if any unknown keys
    are found (suitable for use in CI pipelines).
    """
    if file_path is None:
        discovered = _find_pddrc_file()
        if discovered is None:
            click.echo("No .pddrc found.", err=True)
            raise click.exceptions.Exit(1)
        target = discovered
    else:
        target = Path(file_path)
        if not target.is_file():
            click.echo(f"No such file: {target}", err=True)
            raise click.exceptions.Exit(1)

    try:
        with open(target, "r", encoding="utf-8") as f:
            config = yaml.safe_load(f)
    except yaml.YAMLError as e:
        click.echo(f"YAML syntax error in {target}: {e}", err=True)
        raise click.exceptions.Exit(1)

    if not isinstance(config, dict):
        click.echo(
            f"Invalid .pddrc format in {target}: expected dictionary at root.",
            err=True,
        )
        raise click.exceptions.Exit(1)

    warnings = _collect_pddrc_warnings(config)
    for dotted_path, key in warnings:
        click.echo(
            f"WARNING: .pddrc contains unknown key '{key}' at path "
            f"'{dotted_path}', ignored. Run 'pdd setup' to regenerate."
        )

    click.echo(f"Validation complete: {len(warnings)} warning(s) found.")

    if warnings:
        raise click.exceptions.Exit(1)
