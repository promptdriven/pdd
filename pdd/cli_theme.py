"""Central CLI color system for PDD.

Single source of truth for color across the PDD command-line interface. Every
command should obtain its console from :func:`get_console` (or import the shared
:data:`console`) and style output by *semantic role* — ``command``, ``tag``,
``success``, ``warning``, ``error`` — rather than picking raw colors. Color is
used to communicate meaning, not for decoration.

All values are taken from the PromptDriven.ai Brand Guidelines v1.4, §3 (Color
Palette) and §7 (ASCII & Terminal Assets). See ``docs/design/color-system.md``
for the role -> color mapping and rationale.
"""

from __future__ import annotations

import os

from rich.console import Console
from rich.theme import Theme

# ---------------------------------------------------------------------------
# Brand palette — Brand Guidelines v1.4 §3. Hex values are authoritative; do not
# introduce colors outside this palette.
# ---------------------------------------------------------------------------
ELECTRIC_CYAN = "#00D8FF"      # Primary
DEEP_NAVY = "#0A0A23"          # Ink / Fill
LUMEN_PURPLE = "#8C47FF"       # Accent 1
PROMPT_MAGENTA = "#FF2AA6"     # Accent 2
LIGHT_SLEET = "#F5F7FA"        # Surface-Light
GRAPHITE_900 = "#1A1B26"       # Surface-Dark
BUILD_GREEN = "#18C07A"        # Success
BUILD_GREEN_700 = "#0FA86A"    # Success tint
DIFF_YELLOW = "#FBBB35"        # Warning
BREAK_RED = "#F34842"          # Error

# Human brand name -> hex, for tooling, docs, and round-trip validation.
BRAND_PALETTE = {
    "Electric-Cyan": ELECTRIC_CYAN,
    "Deep-Navy": DEEP_NAVY,
    "Lumen-Purple": LUMEN_PURPLE,
    "Prompt-Magenta": PROMPT_MAGENTA,
    "Light-Sleet": LIGHT_SLEET,
    "Graphite-900": GRAPHITE_900,
    "Build-Green": BUILD_GREEN,
    "Build-Green-700": BUILD_GREEN_700,
    "Diff-Yellow": DIFF_YELLOW,
    "Break-Red": BREAK_RED,
}

# ---------------------------------------------------------------------------
# Semantic roles -> Rich style strings.
#
# The rule the palette encodes:
#   * Commands are the hero of the CLI, so they wear the primary brand color.
#   * Tags / labels / keys take Accent 1 so they stay visually distinct from
#     commands at a glance.
#   * Selections / highlights / CTAs take Accent 2 (used sparingly).
#   * State is green / yellow / red — success / warning / error.
# ---------------------------------------------------------------------------
SEMANTIC_STYLES = {
    # Structure & identifiers (primary / Electric-Cyan)
    "command": ELECTRIC_CYAN,
    "command.strong": f"bold {ELECTRIC_CYAN}",
    "heading": f"bold {ELECTRIC_CYAN}",
    "info": ELECTRIC_CYAN,
    "value": ELECTRIC_CYAN,

    # Tags, labels, keys (Accent 1 / Lumen-Purple)
    "tag": LUMEN_PURPLE,
    "tag.strong": f"bold {LUMEN_PURPLE}",
    "label": LUMEN_PURPLE,

    # Selections, highlights, CTAs (Accent 2 / Prompt-Magenta — use sparingly)
    "accent": PROMPT_MAGENTA,
    "selector": f"bold {PROMPT_MAGENTA}",

    # States
    "success": BUILD_GREEN,
    "success.strong": f"bold {BUILD_GREEN}",
    "version": BUILD_GREEN_700,
    "warning": DIFF_YELLOW,
    "warning.strong": f"bold {DIFF_YELLOW}",
    "error": f"bold {BREAK_RED}",
    "danger": BREAK_RED,

    # Neutral helpers
    "path": f"dim {ELECTRIC_CYAN}",
    "muted": "dim",
}

# Rich theme: any console built with it resolves the role names above as styles,
# so ``console.print("[command]pdd sync[/command] [success]done[/success]")``
# renders consistently everywhere.
PDD_THEME = Theme(SEMANTIC_STYLES)


# ---------------------------------------------------------------------------
# Raw-ANSI helpers.
#
# A few surfaces paint character cells directly (e.g. the ``pdd context`` usage
# box, where one glyph occupies one cell) rather than routing through a Rich
# console. These helpers let those surfaces derive every escape sequence from
# the one brand palette above, so no module hand-writes its own color codes.
# ---------------------------------------------------------------------------
ANSI_RESET = "\033[0m"
ANSI_FAINT = "\033[2m"

# The 6 levels each channel takes in the xterm-256 6x6x6 color cube.
_CUBE_LEVELS = (0, 95, 135, 175, 215, 255)


def _supports_truecolor() -> bool:
    """Whether the terminal renders 24-bit ``38;2;r;g;b`` foreground color.

    24-bit color has no terminfo capability, so the convention is the ``COLORTERM``
    opt-in (``truecolor`` / ``24bit``), which truecolor terminals (iTerm2, modern
    xterms, VS Code) set. Apple Terminal.app — which supports 16/256 color but not
    truecolor — leaves it unset, so we fall back to 256-color there rather than
    emitting sequences it silently drops (the result being *no* color). When unsure
    we downgrade: 256-color renders correctly everywhere truecolor does.
    """
    return os.environ.get("COLORTERM", "").strip().lower() in ("truecolor", "24bit")


def _rgb_to_xterm256(r: int, g: int, b: int) -> int:
    """Nearest xterm-256 palette index for an RGB triple.

    Chooses whichever is closer: the best 6x6x6 color-cube cell (16-231) or the
    24-step grayscale ramp (232-255), by squared RGB distance — so brand hues keep
    their character and near-grays don't get a color cast.
    """
    def nearest_level(v: int) -> int:
        return min(range(6), key=lambda i: abs(_CUBE_LEVELS[i] - v))

    ri, gi, bi = nearest_level(r), nearest_level(g), nearest_level(b)
    cube_rgb = (_CUBE_LEVELS[ri], _CUBE_LEVELS[gi], _CUBE_LEVELS[bi])
    cube_idx = 16 + 36 * ri + 6 * gi + bi

    gray_step = min(23, max(0, round((round((r + g + b) / 3) - 8) / 10)))
    gray_level = 8 + gray_step * 10
    gray_idx = 232 + gray_step

    def dist(c: tuple) -> int:
        return (c[0] - r) ** 2 + (c[1] - g) ** 2 + (c[2] - b) ** 2

    return gray_idx if dist((gray_level,) * 3) < dist(cube_rgb) else cube_idx


def hex_to_ansi(hex_color: str) -> str:
    """Return the ANSI foreground SGR prefix for a ``#RRGGBB`` brand color.

    Emits 24-bit truecolor (``\\033[38;2;r;g;bm``) on terminals that support it so
    the rendered hue is exactly on-brand, and degrades to the nearest xterm-256
    color (``\\033[38;5;nm``) elsewhere — e.g. Apple Terminal.app, which drops
    truecolor sequences and would otherwise show no color at all. Pair the result
    with :data:`ANSI_RESET`. The choice is read from the environment (see
    :func:`_supports_truecolor`); whether to color at all is the caller's decision.
    """
    h = hex_color.lstrip("#")
    r, g, b = int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16)
    if _supports_truecolor():
        return f"\033[38;2;{r};{g};{b}m"
    return f"\033[38;5;{_rgb_to_xterm256(r, g, b)}m"


def get_console(**kwargs) -> Console:
    """Return a Rich ``Console`` pre-configured with the PDD theme.

    Extra keyword arguments are forwarded to ``Console`` (e.g. ``stderr=True``),
    so callers can route to stderr or tweak width while keeping the shared
    palette. A caller-supplied ``theme`` overrides the default.
    """
    kwargs.setdefault("theme", PDD_THEME)
    return Console(**kwargs)


def style(role: str, text: str) -> str:
    """Wrap ``text`` in Rich markup for a semantic ``role``.

    Example: ``style("command", "pdd sync")`` -> ``"[command]pdd sync[/command]"``.
    Useful when building a string for a console that already carries
    :data:`PDD_THEME`.
    """
    return f"[{role}]{text}[/{role}]"


# Shared, ready-to-use themed console for simple call sites.
console = get_console()

__all__ = [
    "ELECTRIC_CYAN",
    "DEEP_NAVY",
    "LUMEN_PURPLE",
    "PROMPT_MAGENTA",
    "LIGHT_SLEET",
    "GRAPHITE_900",
    "BUILD_GREEN",
    "BUILD_GREEN_700",
    "DIFF_YELLOW",
    "BREAK_RED",
    "BRAND_PALETTE",
    "SEMANTIC_STYLES",
    "PDD_THEME",
    "ANSI_RESET",
    "ANSI_FAINT",
    "hex_to_ansi",
    "get_console",
    "style",
    "console",
]
