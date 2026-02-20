#!/usr/bin/env python3
"""Shared utilities for pipeline scripts.

Provides project config loading, progress reporting (JSON lines for SSE),
and common path resolution.
"""

import json
import sys
import time
from pathlib import Path


def get_project_root() -> Path:
    """Return the video_editor project root directory."""
    return Path(__file__).resolve().parent.parent


def load_project_config() -> dict:
    """Load project.json from the project root."""
    config_path = get_project_root() / "project.json"
    if not config_path.exists():
        return {"name": "untitled", "sections": [], "outputResolution": {"width": 1920, "height": 1080}}
    with open(config_path) as f:
        return json.load(f)


def save_project_config(config: dict) -> None:
    """Write project.json to the project root."""
    config_path = get_project_root() / "project.json"
    with open(config_path, "w") as f:
        json.dump(config, f, indent=2)


def get_section(section_id: str) -> dict | None:
    """Return a single section dict by id, or None."""
    config = load_project_config()
    for s in config.get("sections", []):
        if s["id"] == section_id:
            return s
    return None


def get_sections() -> list[dict]:
    """Return the list of all sections from project.json."""
    return load_project_config().get("sections", [])


def emit_progress(step: str, progress: int, message: str = "", **extra) -> None:
    """Emit a JSON-line progress event for SSE streaming.

    The Node.js route reads stdout line-by-line and forwards as SSE.
    """
    event = {
        "step": step,
        "progress": progress,
        "message": message,
        "timestamp": time.strftime("%H:%M:%S"),
        **extra,
    }
    print(json.dumps(event), flush=True)


def emit_error(step: str, error: str) -> None:
    """Emit a JSON-line error event."""
    emit_progress(step, -1, error, status="error")


def emit_done(step: str, message: str = "Complete") -> None:
    """Emit a JSON-line completion event."""
    emit_progress(step, 100, message, status="done")


# Common paths
PROJECT_ROOT = get_project_root()
DATA_DIR = PROJECT_ROOT / "data"
OUTPUTS_DIR = PROJECT_ROOT / ".." / "outputs"
SPECS_DIR = PROJECT_ROOT / ".." / "specs"
NARRATIVE_DIR = PROJECT_ROOT / ".." / "narrative"
REMOTION_DIR = PROJECT_ROOT / ".." / "remotion"
REMOTION_PUBLIC = REMOTION_DIR / "public"
TTS_OUTPUT_DIR = OUTPUTS_DIR / "tts"
VEO_OUTPUT_DIR = OUTPUTS_DIR / "veo"
SECTIONS_OUTPUT_DIR = OUTPUTS_DIR / "sections"
