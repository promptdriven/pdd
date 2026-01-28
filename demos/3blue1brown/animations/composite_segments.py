#!/usr/bin/env python3
"""
Composite left and right video segments into split-screen videos.

Usage:
    python composite_segments.py [--segment SEGMENT_ID]

Requires: ffmpeg installed and in PATH
"""

import argparse
import subprocess
import sys
from pathlib import Path

SEGMENTS = {
    "01a": "establish_split_screen",
    "01b": "synchronized_completion",
    "01c": "brief_satisfaction",
    "01d": "zoom_out_reveal",
    "01e": "hold_accumulated_weight",
}


def check_ffmpeg():
    """Check if ffmpeg is available."""
    try:
        subprocess.run(
            ["ffmpeg", "-version"],
            capture_output=True,
            check=True
        )
        return True
    except (subprocess.CalledProcessError, FileNotFoundError):
        return False


def composite_videos(left_path: Path, right_path: Path, output_path: Path) -> bool:
    """
    Composite two videos side by side with a white divider line.

    Creates a split-screen video with:
    - Left video on left half
    - Right video on right half
    - White vertical line divider in center

    Handles both 16:9 and 9:16 input videos:
    - 9:16 inputs: Stack side by side (no scaling needed)
    - 16:9 inputs: Crop center portion to avoid horizontal squash
    """
    print(f"\nCompositing: {output_path.name}")
    print(f"  Left:  {left_path.name}")
    print(f"  Right: {right_path.name}")

    if not left_path.exists():
        print(f"  Error: Left video not found: {left_path}")
        return False

    if not right_path.exists():
        print(f"  Error: Right video not found: {right_path}")
        return False

    # Check input video dimensions
    probe_cmd = [
        "ffprobe", "-v", "error",
        "-select_streams", "v:0",
        "-show_entries", "stream=width,height",
        "-of", "csv=p=0",
        str(left_path)
    ]
    try:
        result = subprocess.run(probe_cmd, capture_output=True, text=True, check=True)
        width, height = map(int, result.stdout.strip().split(','))
        is_vertical = height > width
        print(f"  Input format: {width}x{height} ({'vertical 9:16' if is_vertical else 'horizontal 16:9'})")
    except Exception:
        is_vertical = False  # Assume horizontal if probe fails

    if is_vertical:
        # 9:16 videos: Stack side by side directly
        # Two 9:16 = 18:16 ≈ 1.125:1, then pad to 16:9
        filter_complex = (
            # Stack horizontally (no scaling - preserves quality)
            "[0:v][1:v]hstack=inputs=2[stacked];"
            # Draw white vertical line in center (2 pixels wide)
            "[stacked]drawbox=x=(iw/2)-1:y=0:w=2:h=ih:color=white:t=fill[lined];"
            # Pad to 16:9 with black bars (letterbox)
            "[lined]pad=w=ih*16/9:h=ih:x=(ow-iw)/2:y=0:color=black[out]"
        )
    else:
        # 16:9 videos: Crop center 50% width from each to avoid squash
        filter_complex = (
            # Crop center portion of left video (half width, full height)
            "[0:v]crop=iw/2:ih:iw/4:0[left];"
            # Crop center portion of right video
            "[1:v]crop=iw/2:ih:iw/4:0[right];"
            # Stack horizontally
            "[left][right]hstack=inputs=2[stacked];"
            # Draw white vertical line in center (2 pixels wide)
            "[stacked]drawbox=x=(iw/2)-1:y=0:w=2:h=ih:color=white:t=fill[out]"
        )

    cmd = [
        "ffmpeg",
        "-y",  # Overwrite output
        "-i", str(left_path),
        "-i", str(right_path),
        "-filter_complex", filter_complex,
        "-map", "[out]",
        "-c:v", "libx264",
        "-preset", "medium",
        "-crf", "18",
        "-pix_fmt", "yuv420p",
        str(output_path)
    ]

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True
        )

        if result.returncode != 0:
            print(f"  Error: ffmpeg failed")
            print(f"  stderr: {result.stderr[:500]}")
            return False

        print(f"  Created: {output_path}")
        return True

    except Exception as e:
        print(f"  Error: {e}")
        return False


def main():
    parser = argparse.ArgumentParser(
        description="Composite left/right video segments into split-screen"
    )
    parser.add_argument(
        "--segment",
        type=str,
        help="Composite only this segment (e.g., 01a, 01b)",
        choices=list(SEGMENTS.keys()),
    )
    args = parser.parse_args()

    # Check ffmpeg
    if not check_ffmpeg():
        print("Error: ffmpeg not found. Please install ffmpeg.")
        print("  macOS: brew install ffmpeg")
        print("  Ubuntu: sudo apt install ffmpeg")
        sys.exit(1)

    # Set up paths
    script_dir = Path(__file__).parent
    output_dir = script_dir / "outputs"
    composite_dir = script_dir / "composited"
    composite_dir.mkdir(exist_ok=True)

    # Determine which segments to process
    segments_to_process = (
        [args.segment] if args.segment else list(SEGMENTS.keys())
    )

    results = {}

    for segment_id in segments_to_process:
        segment_name = SEGMENTS[segment_id]

        left_path = output_dir / f"{segment_id}_{segment_name}_left.mp4"
        right_path = output_dir / f"{segment_id}_{segment_name}_right.mp4"
        output_path = composite_dir / f"{segment_id}_{segment_name}.mp4"

        if not left_path.exists() or not right_path.exists():
            print(f"\nSkipping {segment_id}: missing left/right videos")
            print(f"  Run: python generate_segments.py --separate-sides --segment {segment_id}")
            results[segment_id] = False
            continue

        results[segment_id] = composite_videos(left_path, right_path, output_path)

    # Summary
    print(f"\n{'='*60}")
    print("Composite Summary")
    print(f"{'='*60}")

    for segment_id, success in results.items():
        status = "OK" if success else "SKIPPED/FAILED"
        print(f"  {segment_id}: {status}")

    succeeded = sum(1 for s in results.values() if s)
    total = len(results)
    print(f"\n  Total: {succeeded}/{total} succeeded")

    if succeeded > 0:
        print(f"\nComposited videos saved to: {composite_dir}/")

    if succeeded < total:
        sys.exit(1)


if __name__ == "__main__":
    main()
