from __future__ import annotations

import sys
from pathlib import Path

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.setup.pddrc_initializer import offer_pddrc_init


def main() -> None:
    """
    Demonstrates how to use the pddrc_initializer module to:
    1. Check if .pddrc exists in current project
    2. Detect project language (Python/TypeScript/Go)
    3. Offer to create .pddrc with sensible defaults
    """

    # Run the interactive initialization
    # was_created = offer_pddrc_init()  # Uncomment to run interactively

    # Example flow:
    #   No .pddrc found in current project.
    #
    #   Would you like to create one with default settings?
    #     Default language: python
    #     Output path: pdd/
    #     Test output path: tests/
    #
    #   Create .pddrc? [Y/n]
    #   ✓ Created .pddrc with default settings
    pass


if __name__ == "__main__":
    main()
