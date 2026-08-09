# Curated usage example for PDD prompts that include cli_theme.
# Shows the shared themed console, the semantic markup roles, the style()
# helper, building a fresh console with get_console(), the global color
# preference toggle, and the hex_to_ansi() low-level helper.
# This file is manually maintained — do not regenerate via pdd sync.

from pdd.cli_theme import (
    ELECTRIC_CYAN,
    apply_global_color_preference,
    console,
    get_console,
    hex_to_ansi,
    style,
)

# `console` is a pre-built Rich Console carrying PDD_THEME. Import it directly
# instead of constructing a new Console() so output is consistent everywhere.

# --- Semantic markup roles (use these; never hard-code hex colors) ---
#
#   [command] — command names / identifiers   (Electric-Cyan)
#   [heading] — section titles                 (bold Electric-Cyan)
#   [info]    — neutral informational text     (Electric-Cyan)
#   [tag]     — tags / labels / keys           (Lumen-Purple)
#   [success] / [success.strong] — success     (Build-Green)
#   [warning] — warnings                       (Diff-Yellow)
#   [error]   — bold error text                (bold Break-Red)
#   [path]    — file paths and URLs            (dim Electric-Cyan)
#   [muted]   — secondary / dim text           (dim)


def show_command_summary(command: str, ok: bool, target: str) -> None:
    """Print a themed one-line summary for a finished command."""
    console.rule(f"[heading]{command}[/heading]", style="muted")
    state = "[success.strong]✓ done[/success.strong]" if ok else "[error]✗ failed[/error]"
    # style() is handy when composing a string for a console that already
    # carries PDD_THEME — it just wraps text in the role's markup tags.
    console.print(f"  {style('command', command)}  ->  {state}")
    console.print(f"  [muted]target:[/muted] [path]{target}[/path]")


def render_without_color() -> str:
    """Capture output from a throwaway console that has color disabled.

    get_console(**kwargs) returns a Console pre-loaded with PDD_THEME while
    still honoring the active global color preference. A short-lived
    --no-color scope is applied so the captured text is plain (no ANSI).
    """
    restore = apply_global_color_preference(False)
    try:
        plain = get_console()
        with plain.capture() as cap:
            plain.print("[success]themed but color-disabled[/success]")
        return cap.get()
    finally:
        # Preference changes are invocation-scoped; always restore.
        restore()


if __name__ == "__main__":
    show_command_summary("pdd sync cli_theme", ok=True, target="pdd/cli_theme.py")
    console.print(render_without_color(), end="")
    # hex_to_ansi() drops to a raw ANSI escape for the rare call site that
    # writes to a plain stream instead of a themed console.
    console.print(f"raw ansi for primary: {hex_to_ansi(ELECTRIC_CYAN)!r}")
