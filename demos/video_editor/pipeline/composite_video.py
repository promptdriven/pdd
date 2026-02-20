#!/usr/bin/env python3
"""Composite left/right video segments into split-screen videos using ffmpeg.

Usage:
    python composite_video.py --section cold_open        # Composite one section
    python composite_video.py --section all              # All sections
"""

import argparse
import subprocess
import sys
from pathlib import Path

from utils import (
    VEO_OUTPUT_DIR, load_project_config, get_sections,
    emit_progress, emit_error, emit_done,
)


def check_ffmpeg() -> bool:
    """Check if ffmpeg is available."""
    try:
        subprocess.run(["ffmpeg", "-version"], capture_output=True, check=True)
        return True
    except (subprocess.CalledProcessError, FileNotFoundError):
        return False


def composite_videos(left_path: Path, right_path: Path, output_path: Path) -> bool:
    """Composite two videos side by side with a white divider.

    Handles both 9:16 (vertical) and 16:9 (horizontal) inputs.
    """
    if not left_path.exists() or not right_path.exists():
        return False

    # Check input dimensions
    try:
        result = subprocess.run(
            ["ffprobe", "-v", "error", "-select_streams", "v:0",
             "-show_entries", "stream=width,height", "-of", "csv=p=0",
             str(left_path)],
            capture_output=True, text=True, check=True,
        )
        width, height = map(int, result.stdout.strip().split(","))
        is_vertical = height > width
    except Exception:
        is_vertical = False

    if is_vertical:
        filter_complex = (
            "[0:v][1:v]hstack=inputs=2[stacked];"
            "[stacked]drawbox=x=(iw/2)-1:y=0:w=2:h=ih:color=white:t=fill[lined];"
            "[lined]pad=w=ih*16/9:h=ih:x=(ow-iw)/2:y=0:color=black[out]"
        )
    else:
        filter_complex = (
            "[0:v]crop=iw/2:ih:iw/4:0[left];"
            "[1:v]crop=iw/2:ih:iw/4:0[right];"
            "[left][right]hstack=inputs=2[stacked];"
            "[stacked]drawbox=x=(iw/2)-1:y=0:w=2:h=ih:color=white:t=fill[out]"
        )

    cmd = [
        "ffmpeg", "-y",
        "-i", str(left_path), "-i", str(right_path),
        "-filter_complex", filter_complex,
        "-map", "[out]",
        "-c:v", "libx264", "-preset", "medium", "-crf", "18",
        "-pix_fmt", "yuv420p",
        str(output_path),
    ]

    result = subprocess.run(cmd, capture_output=True, text=True)
    return result.returncode == 0


def main():
    parser = argparse.ArgumentParser(description="Composite split-screen videos")
    parser.add_argument("--section", default="all", help="Section ID or 'all'")
    args = parser.parse_args()

    if not check_ffmpeg():
        emit_error("veo", "ffmpeg not found. Install: brew install ffmpeg")
        sys.exit(1)

    sections = get_sections()
    if args.section != "all":
        sections = [s for s in sections if s["id"] == args.section]

    results = {}
    for i, section in enumerate(sections):
        pct = int(10 + 80 * (i / max(1, len(sections))))
        raw_dir = VEO_OUTPUT_DIR / section["specDir"] / "raw"
        comp_dir = VEO_OUTPUT_DIR / section["specDir"] / "composited"
        comp_dir.mkdir(parents=True, exist_ok=True)

        # Find left/right pairs
        pairs_found = False
        if raw_dir.exists():
            for left in sorted(raw_dir.glob("*_left.mp4")):
                stem = left.name.replace("_left.mp4", "")
                right = raw_dir / f"{stem}_right.mp4"
                if right.exists():
                    pairs_found = True
                    output = comp_dir / f"{stem}.mp4"
                    emit_progress("veo", pct, f"Compositing {stem}...")
                    success = composite_videos(left, right, output)
                    results[stem] = success

        if not pairs_found:
            emit_progress("veo", pct, f"No left/right pairs for {section['id']}")

    succeeded = sum(1 for s in results.values() if s)
    total = len(results)
    if total == 0:
        emit_done("veo", "No video pairs found to composite")
    elif succeeded == total:
        emit_done("veo", f"Composited {total} video(s)")
    else:
        emit_error("veo", f"{succeeded}/{total} composited")
        sys.exit(1)


if __name__ == "__main__":
    main()
