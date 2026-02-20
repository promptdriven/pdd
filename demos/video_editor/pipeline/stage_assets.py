#!/usr/bin/env python3
"""Stage assets to Remotion public directory for rendering.

Copies generated assets (TTS audio, Veo clips, references) to the
Remotion public/ directory where staticFile() can access them.

Usage:
    python stage_assets.py                      # Stage all assets
    python stage_assets.py --section cold_open  # Stage one section
"""

import argparse
import shutil
import sys
from pathlib import Path

from utils import (
    TTS_OUTPUT_DIR, VEO_OUTPUT_DIR, REMOTION_PUBLIC,
    load_project_config, get_sections,
    emit_progress, emit_error, emit_done,
)


def stage_audio(section: dict) -> list[str]:
    """Copy narration audio files to Remotion public dir."""
    staged = []
    tts_dir = TTS_OUTPUT_DIR / section["specDir"]
    if not tts_dir.exists():
        return staged

    for wav in tts_dir.glob("*_narration.wav"):
        dest = REMOTION_PUBLIC / wav.name
        shutil.copy2(wav, dest)
        staged.append(wav.name)

    return staged


def stage_veo_clips(section: dict) -> list[str]:
    """Copy composited or raw Veo clips to Remotion public dir."""
    staged = []

    # Prefer composited clips, fall back to raw
    for subdir in ["composited", "raw"]:
        clip_dir = VEO_OUTPUT_DIR / section["specDir"] / subdir
        if clip_dir.exists():
            for mp4 in clip_dir.glob("*.mp4"):
                dest = REMOTION_PUBLIC / mp4.name
                shutil.copy2(mp4, dest)
                staged.append(mp4.name)
            if staged:
                break

    return staged


def main():
    parser = argparse.ArgumentParser(description="Stage assets to Remotion public/")
    parser.add_argument("--section", default="all", help="Section ID or 'all'")
    args = parser.parse_args()

    REMOTION_PUBLIC.mkdir(parents=True, exist_ok=True)

    sections = get_sections()
    if args.section != "all":
        sections = [s for s in sections if s["id"] == args.section]

    total_staged = 0
    for i, section in enumerate(sections):
        pct = int(10 + 80 * (i / max(1, len(sections))))
        emit_progress("asset-staging", pct, f"Staging {section['label']}...")

        audio_files = stage_audio(section)
        veo_files = stage_veo_clips(section)
        count = len(audio_files) + len(veo_files)
        total_staged += count
        emit_progress("asset-staging", pct, f"  {section['id']}: {count} file(s)")

    emit_done("asset-staging", f"Staged {total_staged} asset(s) to remotion/public/")


if __name__ == "__main__":
    main()
