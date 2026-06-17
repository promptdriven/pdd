"""Tests for the central PDD CLI color system (pdd/cli_theme.py).

These lock the palette to the PromptDriven.ai Brand Guidelines v1.4 hex values
and verify that every semantic role resolves to a valid Rich style, so commands,
tags, and states stay consistent across the CLI.
"""

import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

from io import StringIO

import pytest
from rich.theme import Theme

from pdd import cli_theme


# ---------------------------------------------------------------------------
# Palette: must match the brand guidelines exactly
# ---------------------------------------------------------------------------

# Brand name -> hex from Brand Guidelines v1.4 §3.
EXPECTED_PALETTE = {
    "Electric-Cyan": "#00D8FF",
    "Deep-Navy": "#0A0A23",
    "Lumen-Purple": "#8C47FF",
    "Prompt-Magenta": "#FF2AA6",
    "Light-Sleet": "#F5F7FA",
    "Graphite-900": "#1A1B26",
    "Build-Green": "#18C07A",
    "Build-Green-700": "#0FA86A",
    "Diff-Yellow": "#FBBB35",
    "Break-Red": "#F34842",
}


def test_brand_palette_matches_guidelines():
    assert cli_theme.BRAND_PALETTE == EXPECTED_PALETTE


@pytest.mark.parametrize("hex_value", EXPECTED_PALETTE.values())
def test_palette_values_are_six_digit_hex(hex_value):
    assert hex_value.startswith("#")
    assert len(hex_value) == 7
    int(hex_value[1:], 16)  # raises ValueError if not valid hex


def test_named_constants_match_palette():
    assert cli_theme.ELECTRIC_CYAN == "#00D8FF"
    assert cli_theme.LUMEN_PURPLE == "#8C47FF"
    assert cli_theme.PROMPT_MAGENTA == "#FF2AA6"
    assert cli_theme.BUILD_GREEN == "#18C07A"
    assert cli_theme.BUILD_GREEN_700 == "#0FA86A"
    assert cli_theme.DIFF_YELLOW == "#FBBB35"
    assert cli_theme.BREAK_RED == "#F34842"


# ---------------------------------------------------------------------------
# Semantic roles and theme
# ---------------------------------------------------------------------------

# Roles every command relies on, including the legacy names kept for back-compat.
REQUIRED_ROLES = [
    "command", "command.strong", "heading", "info", "value",
    "tag", "tag.strong", "label",
    "accent", "selector",
    "success", "success.strong", "version",
    "warning", "warning.strong", "error", "danger",
    "path", "muted",
]


def test_pdd_theme_is_a_rich_theme():
    assert isinstance(cli_theme.PDD_THEME, Theme)


@pytest.mark.parametrize("role", REQUIRED_ROLES)
def test_every_required_role_is_defined(role):
    assert role in cli_theme.SEMANTIC_STYLES


@pytest.mark.parametrize("role", REQUIRED_ROLES)
def test_every_role_resolves_to_a_valid_style(role):
    console = cli_theme.get_console()
    # Console.get_style raises rich.errors.MissingStyle / StyleSyntaxError on a
    # bad name or definition; a clean return means the role is valid.
    assert console.get_style(role) is not None


def test_backward_compatible_role_names_present():
    # The four ad-hoc themes this module replaces used exactly these names.
    for legacy in ("info", "warning", "error", "success", "path", "selector"):
        assert legacy in cli_theme.SEMANTIC_STYLES


def test_meaning_mapping_is_intentional():
    # Commands are the hero color; tags read distinctly; states are green/red.
    assert cli_theme.ELECTRIC_CYAN in cli_theme.SEMANTIC_STYLES["command"]
    assert cli_theme.LUMEN_PURPLE in cli_theme.SEMANTIC_STYLES["tag"]
    assert cli_theme.BUILD_GREEN in cli_theme.SEMANTIC_STYLES["success"]
    assert cli_theme.BREAK_RED in cli_theme.SEMANTIC_STYLES["error"]
    # command and tag must not share a color, or they would not be distinct.
    assert cli_theme.SEMANTIC_STYLES["command"] != cli_theme.SEMANTIC_STYLES["tag"]


# ---------------------------------------------------------------------------
# Console factory and style helper
# ---------------------------------------------------------------------------

def test_get_console_applies_theme():
    assert cli_theme.get_console().get_style("command") is not None


def test_get_console_forwards_kwargs():
    console = cli_theme.get_console(stderr=True)
    assert console.stderr is True


def test_get_console_allows_theme_override():
    custom = Theme({"command": "red"})
    console = cli_theme.get_console(theme=custom)
    # Override wins, but unrelated rendering still works.
    assert console.get_style("command") is not None


def test_shared_console_is_themed():
    assert cli_theme.console.get_style("tag") is not None


def test_style_wraps_markup():
    assert cli_theme.style("command", "pdd sync") == "[command]pdd sync[/command]"
    assert cli_theme.style("error", "boom") == "[error]boom[/error]"


def test_roles_render_ansi_on_a_truecolor_console():
    console = cli_theme.get_console(
        file=StringIO(), force_terminal=True, color_system="truecolor", width=80
    )
    console.print("[command]pdd[/command] [tag]<include>[/tag] [success]ok[/success]")
    out = console.file.getvalue()
    assert "\x1b[" in out  # ANSI escape sequence emitted


# ---------------------------------------------------------------------------
# Issue #1634: brand palette locking for additional semantic roles
# (EPIC #1540 — workstream 1)
# ---------------------------------------------------------------------------

def test_warning_role_resolves_to_diff_yellow():
    """warning state maps to Diff-Yellow from the brand palette (not a generic yellow)."""
    assert cli_theme.DIFF_YELLOW in cli_theme.SEMANTIC_STYLES["warning"]


def test_danger_role_resolves_to_break_red():
    """danger role uses Break-Red — the brand error / failure color."""
    assert cli_theme.BREAK_RED in cli_theme.SEMANTIC_STYLES["danger"]


def test_label_role_resolves_to_lumen_purple():
    """label (Accent-1 family, same as tag) is Lumen-Purple."""
    assert cli_theme.LUMEN_PURPLE in cli_theme.SEMANTIC_STYLES["label"]


def test_accent_role_resolves_to_prompt_magenta():
    """accent (Accent-2 / CTA) is Prompt-Magenta — used sparingly."""
    assert cli_theme.PROMPT_MAGENTA in cli_theme.SEMANTIC_STYLES["accent"]


def test_version_role_resolves_to_build_green_700():
    """version uses the Build-Green-700 tint, distinct from the success base green."""
    assert cli_theme.BUILD_GREEN_700 in cli_theme.SEMANTIC_STYLES["version"]
