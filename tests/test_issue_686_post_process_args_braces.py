"""Regression test for Issue #686: post_process_args brace corruption.

Bug: architecture_json.prompt used {{INPUT_FILE}} but _subst_arg does
.replace('{INPUT_FILE}', val), which partially matches inside double braces
and leaves literal braces in the path: '{/path/to/file}' → FileNotFoundError.

Fix: Templates must use single braces {KEY} in post_process_args.
"""

import re
from pathlib import Path

from pdd.code_generator_main import _parse_front_matter

TEMPLATES_DIR = Path(__file__).resolve().parent.parent / "pdd" / "templates"

# Matches {{ANYTHING}} — the pattern that caused #686
DOUBLE_BRACE_RE = re.compile(r"\{\{[A-Z_]+\}\}")


def test_no_template_uses_double_braces_in_post_process_args() -> None:
    """Scan ALL templates for double-brace placeholders in post_process_args.

    Catches the #686 class of bug in any template, not just architecture_json.
    """
    violations: list[str] = []

    for prompt_file in TEMPLATES_DIR.rglob("*.prompt"):
        text = prompt_file.read_text(encoding="utf-8")
        meta, _ = _parse_front_matter(text)
        if meta is None:
            continue
        fm_args = meta.get("post_process_args", [])
        for arg in fm_args:
            if DOUBLE_BRACE_RE.search(arg):
                rel = prompt_file.relative_to(TEMPLATES_DIR)
                violations.append(f"{rel}: {arg!r}")

    assert not violations, (
        "Templates with double-brace placeholders in post_process_args "
        "(causes #686 path corruption):\n  " + "\n  ".join(violations)
    )
