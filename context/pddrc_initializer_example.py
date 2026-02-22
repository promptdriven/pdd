from __future__ import annotations

import sys
from pathlib import Path

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.pddrc_initializer import _build_pddrc_content, _detect_language


def main() -> None:
    """
    Demonstrates how to use the pddrc_initializer module.

    The primary entry points are:
    - _detect_language(cwd): returns "python", "typescript", "go", or None
    - _build_pddrc_content(language): returns YAML string for .pddrc
    - offer_pddrc_init(): interactive flow with YAML preview + confirmation

    In practice, `pdd setup` imports _detect_language and _build_pddrc_content
    directly for a streamlined flow (no YAML preview).
    """

    # Detect language from marker files in cwd
    from pathlib import Path
    language = _detect_language(Path.cwd())
    print(f"Detected language: {language}")  # e.g. "python" or None

    # Build .pddrc content for a given language
    content = _build_pddrc_content(language or "python")
    print(content)

    # Or use the full interactive flow (shows YAML preview, asks for confirmation):
    # from pdd.pddrc_initializer import offer_pddrc_init
    # was_created = offer_pddrc_init()
    pass


if __name__ == "__main__":
    main()
