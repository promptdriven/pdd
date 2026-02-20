#!/usr/bin/env python3
"""Stitch rendered section videos into a single full video using ffmpeg.

Concatenates all section MP4 files (in order) into outputs/full_video.mp4.

Usage:
    python stitch_video.py                  # Stitch all sections
    python stitch_video.py --output out.mp4 # Custom output path
"""

import argparse
import subprocess
import sys
import tempfile
from pathlib import Path

from utils import (
    OUTPUTS_DIR, SECTIONS_OUTPUT_DIR,
    load_project_config, get_sections,
    emit_progress, emit_error, emit_done,
)


def check_ffmpeg() -> bool:
    """Check if ffmpeg is available."""
    try:
        subprocess.run(["ffmpeg", "-version"], capture_output=True, check=True)
        return True
    except (subprocess.CalledProcessError, FileNotFoundError):
        return False


def main():
    parser = argparse.ArgumentParser(description="Stitch section videos into full video")
    parser.add_argument("--output", help="Output file path (default: outputs/full_video.mp4)")
    args = parser.parse_args()

    if not check_ffmpeg():
        emit_error("stitch", "ffmpeg not found. Install: brew install ffmpeg")
        sys.exit(1)

    sections = get_sections()
    output_path = Path(args.output) if args.output else OUTPUTS_DIR / "full_video.mp4"
    OUTPUTS_DIR.mkdir(parents=True, exist_ok=True)

    # Collect section video files in order
    video_files = []
    for section in sections:
        video_path = SECTIONS_OUTPUT_DIR / section["videoFile"]
        if video_path.exists():
            video_files.append(video_path)
        else:
            emit_progress("stitch", 0, f"Warning: {section['videoFile']} not found, skipping")

    if not video_files:
        emit_error("stitch", "No section videos found to stitch")
        sys.exit(1)

    emit_progress("stitch", 10, f"Stitching {len(video_files)} section(s)...")

    # Create ffmpeg concat file
    with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as f:
        for vf in video_files:
            f.write(f"file '{vf.resolve()}'\n")
        concat_file = f.name

    cmd = [
        "ffmpeg", "-y",
        "-f", "concat", "-safe", "0",
        "-i", concat_file,
        "-c", "copy",
        str(output_path),
    ]

    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
        if result.returncode != 0:
            emit_error("stitch", f"ffmpeg failed: {result.stderr[:200]}")
            sys.exit(1)

        emit_done("stitch", f"Stitched {len(video_files)} sections -> {output_path.name}")

    except subprocess.TimeoutExpired:
        emit_error("stitch", "ffmpeg timed out")
        sys.exit(1)
    finally:
        Path(concat_file).unlink(missing_ok=True)


if __name__ == "__main__":
    main()
