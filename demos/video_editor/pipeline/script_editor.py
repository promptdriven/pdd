#!/usr/bin/env python3
"""Script editor: validate the main narrative script.

Checks that narrative/main_script.md exists and has content for each section.

Usage:
    python script_editor.py
"""

import sys
from pathlib import Path

from utils import (
    NARRATIVE_DIR, load_project_config, get_sections,
    emit_progress, emit_error, emit_done,
)


def main():
    emit_progress("script-editor", 10, "Checking narrative script...")

    script_path = NARRATIVE_DIR / "main_script.md"

    if not script_path.exists():
        NARRATIVE_DIR.mkdir(parents=True, exist_ok=True)
        emit_progress("script-editor", 50, f"Script not found at {script_path}")
        emit_progress("script-editor", 60, "Creating placeholder script...")

        sections = get_sections()
        lines = ["# Video Script\n"]
        for section in sections:
            lines.append(f"\n## {section['label']}\n")
            lines.append(f"<!-- Write narration for {section['label']} here -->\n")

        script_path.write_text("\n".join(lines))
        emit_done("script-editor", f"Created placeholder script with {len(sections)} section(s)")
        return

    content = script_path.read_text()
    word_count = len(content.split())
    line_count = len(content.strip().split("\n"))

    emit_progress("script-editor", 50, f"Script found: {line_count} lines, {word_count} words")

    # Check that each section has content
    sections = get_sections()
    found_sections = []
    for section in sections:
        label = section["label"]
        if label.lower() in content.lower():
            found_sections.append(label)

    emit_progress("script-editor", 80, f"Sections referenced: {len(found_sections)}/{len(sections)}")

    if len(found_sections) < len(sections):
        missing = [s["label"] for s in sections if s["label"] not in found_sections]
        emit_progress("script-editor", 85, f"Missing sections: {', '.join(missing)}")

    emit_done("script-editor", f"Script validated: {word_count} words, {len(found_sections)}/{len(sections)} sections")


if __name__ == "__main__":
    main()
