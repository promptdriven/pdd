#!/usr/bin/env python3
"""Project setup: validate and initialize project structure.

Ensures all required directories exist and project.json is valid.

Usage:
    python project_setup.py
"""

import sys
from pathlib import Path

from utils import (
    PROJECT_ROOT, DATA_DIR, OUTPUTS_DIR, SPECS_DIR, NARRATIVE_DIR, REMOTION_DIR,
    SECTIONS_OUTPUT_DIR, TTS_OUTPUT_DIR, VEO_OUTPUT_DIR, REMOTION_PUBLIC,
    load_project_config, emit_progress, emit_error, emit_done,
)


def main():
    emit_progress("project-setup", 10, "Validating project.json...")

    config = load_project_config()
    if not config.get("sections"):
        emit_error("project-setup", "No sections defined in project.json")
        sys.exit(1)

    emit_progress("project-setup", 30, f"Found {len(config['sections'])} section(s)")

    # Ensure all required directories exist
    dirs = [
        DATA_DIR,
        OUTPUTS_DIR,
        SECTIONS_OUTPUT_DIR,
        TTS_OUTPUT_DIR,
        VEO_OUTPUT_DIR,
        SPECS_DIR,
        NARRATIVE_DIR,
    ]

    emit_progress("project-setup", 50, "Creating directories...")
    created = 0
    for d in dirs:
        d.mkdir(parents=True, exist_ok=True)
        if not d.exists():
            emit_error("project-setup", f"Failed to create {d}")
            sys.exit(1)
        created += 1

    # Validate section config
    emit_progress("project-setup", 70, "Validating sections...")
    for section in config["sections"]:
        required = ["id", "label", "videoFile", "specDir", "remotionDir", "compositionId"]
        missing = [k for k in required if not section.get(k)]
        if missing:
            emit_progress("project-setup", 70, f"Warning: section '{section.get('id', '?')}' missing: {missing}")

    # Check for TTS config
    if config.get("tts"):
        emit_progress("project-setup", 85, f"TTS engine: {config['tts'].get('engine', 'not set')}")

    # Check for Veo config
    if config.get("veo"):
        emit_progress("project-setup", 90, f"Veo model: {config['veo'].get('model', 'not set')}")

    emit_done("project-setup", f"Project ready: {len(config['sections'])} sections, {created} directories")


if __name__ == "__main__":
    main()
