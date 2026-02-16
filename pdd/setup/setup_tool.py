"""
Main orchestrator for ``pdd setup``.

Auto-scans the environment for API keys (existence only — no API calls),
then presents an interactive menu.  After any action the menu re-displays
with an updated scan.
"""
from __future__ import annotations

from typing import Dict

from .api_key_scanner import scan_environment, KeyInfo
from .provider_manager import (
    add_provider_from_registry,
    add_custom_provider,
    remove_models_by_provider,
    remove_individual_models,
)
from .local_llm_configurator import configure_local_llm
from .model_tester import test_model_interactive
from .cli_detector import detect_cli_tools
from .pddrc_initializer import offer_pddrc_init


# ---------------------------------------------------------------------------
# Display helpers
# ---------------------------------------------------------------------------

def _display_scan(scan_results: Dict[str, KeyInfo]) -> None:
    """Print a table of discovered API keys and a summary line."""
    print("\n  API-key scan")
    print("  " + "─" * 50)

    if not scan_results:
        print("    No models configured yet.")
        print("    Use 'Add a provider' to get started.")
        print()
        return

    api_found = 0
    local_count = 0

    for key_name, info in scan_results.items():
        if info.is_set:
            # Heuristic: keys whose source mentions "local" or whose name
            # hints at a local provider are counted separately.
            source_lower = (info.source or "").lower()
            if "local" in source_lower or "ollama" in key_name.lower() or "lm_studio" in key_name.lower():
                local_count += 1
            else:
                api_found += 1
            print(f"    {key_name:30s} ✓ Found  ({info.source})")
        else:
            print(f"    {key_name:30s} — Not found")

    total_configured = api_found + local_count
    print(
        f"\n  Models configured: {total_configured} "
        f"(from {api_found} API keys + {local_count} local)"
    )
    print()


def _display_menu() -> None:
    """Print the interactive menu options."""
    print("  What would you like to do?")
    print("    1. Add a provider")
    print("    2. Remove models")
    print("    3. Test a model")
    print("    4. Detect CLI tools")
    print("    5. Initialize .pddrc")
    print("    6. Done")
    print()


def _add_provider_submenu() -> None:
    """Sub-menu for option 1 — Add a provider."""
    print()
    print("  Add a provider:")
    print("    a. Search providers")
    print("    b. Add a local LLM")
    print("    c. Add a custom provider")
    print()

    sub_choice = input("  Choice [a/b/c]: ").strip().lower()

    if sub_choice == "a":
        add_provider_from_registry()
    elif sub_choice == "b":
        configure_local_llm()
    elif sub_choice == "c":
        add_custom_provider()
    else:
        print("  Invalid choice — returning to main menu.")


def _remove_models_submenu() -> None:
    """Sub-menu for option 2 — Remove models."""
    print()
    print("  Remove models:")
    print("    a. By provider")
    print("    b. Individual models")
    print()

    sub_choice = input("  Choice [a/b]: ").strip().lower()

    if sub_choice == "a":
        remove_models_by_provider()
    elif sub_choice == "b":
        remove_individual_models()
    else:
        print("  Invalid choice — returning to main menu.")


# ---------------------------------------------------------------------------
# Public entry point
# ---------------------------------------------------------------------------

def run_setup() -> None:
    """Main entry point for ``pdd setup``.

    Scans the environment, displays results, and loops an interactive menu
    until the user selects *Done* or presses Ctrl-C.
    """
    try:
        print()
        print("  ╭──────────────────────────────╮")
        print("  │        pdd setup             │")
        print("  ╰──────────────────────────────╯")

        while True:
            # (Re-)scan on every iteration so the display stays current.
            scan_results = scan_environment()
            _display_scan(scan_results)
            _display_menu()

            choice = input("  Choice [1-6]: ").strip()

            if choice == "1":
                _add_provider_submenu()
            elif choice == "2":
                _remove_models_submenu()
            elif choice == "3":
                test_model_interactive()
            elif choice == "4":
                detect_cli_tools()
            elif choice == "5":
                offer_pddrc_init()
            elif choice == "6":
                print("\n  ✓ Setup complete. Happy prompting!\n")
                break
            else:
                print("  Invalid choice — please enter a number between 1 and 6.")

    except KeyboardInterrupt:
        # Clean exit on Ctrl-C at any point.
        print("\n\n  Setup interrupted — exiting.\n")


if __name__ == "__main__":
    run_setup()