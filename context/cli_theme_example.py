# Curated usage example for PDD prompts that include cli_theme.
# Shows canonical console, console.rule(), and PDD_THEME semantic markup roles.
# This file is manually maintained — do not regenerate via pdd sync.

from pdd.cli_theme import console, PDD_THEME

# console is a pre-built Rich Console configured with PDD_THEME.
# Import it directly instead of constructing a new one.

# --- Semantic markup roles (use these; never hard-code hex colors) ---
#
#   [path]    — file paths and URLs          (dim Electric-Cyan)
#   [muted]   — labels, secondary info       (dim)
#   [info]    — neutral informational text   (Electric-Cyan)
#   [success.strong] — bold success output   (bold Build-Green)
#   [error]   — bold error text              (bold Break-Red)
#   [command] — command names / identifiers  (Electric-Cyan)

def show_server_info(host: str, port: int, target_url: str) -> None:
    """Print a themed server-info block after the setup phase."""
    # Visual separator: marks the boundary between setup and running state.
    console.rule("[muted]Server running[/muted]", style="muted")

    # URL block: labels in [muted], values in [path].
    console.print(f"  [muted]Local:[/muted]     [path]http://{host}:{port}[/path]")
    console.print(f"  [muted]API docs:[/muted]  [path]http://{host}:{port}/docs[/path]")
    console.print(f"  [muted]Frontend:[/muted]  [path]{target_url}[/path]")
    console.print("  [muted]Stop:[/muted]      Ctrl+C")
