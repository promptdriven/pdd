#!/usr/bin/env python3
"""
Generate segment 07 (split screen sepia) for section 02.

This segment is a callback to the cold open, so it uses the last frames from
segment 01e as reference images for character consistency.

Usage:
    python generate_segment_07.py --generate-videos  # Generate videos using cold open frames
    python generate_segment_07.py --composite        # Composite with sepia effect
    python generate_segment_07.py --all              # Do everything

Reference Frames:
    By default, uses frames from the cold open (01e):
    - animations/frames/01e_left_last.png (developer)
    - animations/frames/01e_right_last.png (grandmother)

    To use custom reference images instead:
    python generate_segment_07.py --generate-videos --custom-refs
"""

import argparse
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

try:
    from google import genai
    from google.genai import types
except ImportError:
    print("Error: google-genai not installed. Run: pip install google-genai")
    sys.exit(1)

# Paths
SCRIPT_DIR = Path(__file__).parent
PROMPTS_DIR = SCRIPT_DIR / "prompts"
REFS_DIR = SCRIPT_DIR / "references"
OUTPUTS_DIR = SCRIPT_DIR / "outputs"
COMPOSITED_DIR = SCRIPT_DIR / "composited"
FRAMES_DIR = SCRIPT_DIR / "frames"

# Cold open frames directory (source for character consistency)
# Path: demos/3blue1brown/animations/frames/ (from demos/3blue1brown/my-video/animations/02/)
COLD_OPEN_FRAMES_DIR = (SCRIPT_DIR / ".." / ".." / ".." / "animations" / "frames").resolve()

# Vertex AI settings
DEFAULT_PROJECT = "prompt-driven-development"
DEFAULT_LOCATION = "us-central1"


def get_client():
    """Initialize Vertex AI client."""
    creds_path = os.environ.get("GOOGLE_APPLICATION_CREDENTIALS")
    if not creds_path:
        print("Error: GOOGLE_APPLICATION_CREDENTIALS not set")
        sys.exit(1)

    project = DEFAULT_PROJECT
    try:
        with open(creds_path) as f:
            project = json.load(f).get("project_id", DEFAULT_PROJECT)
    except Exception:
        pass

    print(f"Using Vertex AI: project={project}, location={DEFAULT_LOCATION}")
    return genai.Client(vertexai=True, project=project, location=DEFAULT_LOCATION)


def extract_veo_prompt(md_path: Path) -> str:
    """Extract Veo prompt from markdown file."""
    content = md_path.read_text()
    pattern = r"## Veo Prompt\s*```\s*(.*?)\s*```"
    match = re.search(pattern, content, re.DOTALL)
    return match.group(1).strip() if match else ""


def get_reference_frames(use_custom: bool = False):
    """Get reference frame paths for character consistency.

    By default, uses last frames from cold open segment 01e.
    If use_custom=True, uses locally generated reference images.

    Returns:
        tuple: (left_frame_path, right_frame_path) or (None, None) if not found
    """
    if use_custom:
        # Use locally generated reference images
        left_path = REFS_DIR / "developer_reference.png"
        right_path = REFS_DIR / "grandmother_reference.png"
    else:
        # Use last frames from cold open segment 01e
        left_path = COLD_OPEN_FRAMES_DIR / "01e_left_last.png"
        right_path = COLD_OPEN_FRAMES_DIR / "01e_right_last.png"

    print(f"\n=== Reference Frames ===")
    print(f"  Left (developer):   {left_path}")
    print(f"  Right (grandmother): {right_path}")

    if not left_path.exists():
        print(f"  ERROR: Left reference not found: {left_path}")
        return None, None
    if not right_path.exists():
        print(f"  ERROR: Right reference not found: {right_path}")
        return None, None

    print(f"  Both reference frames found.")
    return left_path, right_path


def load_image(path: Path):
    """Load image for Veo input."""
    if not path.exists():
        return None
    with open(path, "rb") as f:
        return types.Image(image_bytes=f.read(), mime_type="image/png")


def generate_video(client, prompt: str, output_path: Path, reference_image=None):
    """Generate a video using Veo."""
    print(f"\nGenerating: {output_path.name}")
    print(f"  Prompt: {prompt[:80]}...")

    try:
        gen_kwargs = {
            "model": "veo-3.1-generate-preview",
            "prompt": prompt,
            "config": types.GenerateVideosConfig(
                aspect_ratio="9:16",
                number_of_videos=1,
            ),
        }
        if reference_image:
            gen_kwargs["image"] = reference_image
            print("  Using reference image")

        operation = client.models.generate_videos(**gen_kwargs)
        print(f"  Operation: {operation.name}")

        elapsed = 0
        while not operation.done:
            print(f"  Waiting... ({elapsed}s)")
            time.sleep(20)
            elapsed += 20
            operation = client.operations.get(operation)
            if elapsed > 600:
                print("  Timeout!")
                return False

        if operation.error:
            print(f"  Error: {operation.error}")
            return False

        if operation.response and operation.response.generated_videos:
            video = operation.response.generated_videos[0].video
            if hasattr(video, 'video_bytes') and video.video_bytes:
                with open(output_path, "wb") as f:
                    f.write(video.video_bytes)
                print(f"  Saved: {output_path}")
                return True

        print("  Error: No video generated")
        return False

    except Exception as e:
        print(f"  Error: {e}")
        import traceback
        traceback.print_exc()
        return False


def generate_videos(client, use_custom_refs: bool = False):
    """Generate left and right videos using reference frames for consistency.

    Args:
        client: Vertex AI client
        use_custom_refs: If True, use locally generated refs instead of cold open frames
    """
    print("\n=== Generating Videos ===")
    OUTPUTS_DIR.mkdir(exist_ok=True)

    # Get reference frame paths
    left_ref_path, right_ref_path = get_reference_frames(use_custom=use_custom_refs)
    if not left_ref_path or not right_ref_path:
        print("Error: Reference frames not found.")
        print("  Expected cold open frames at: animations/frames/01e_*_last.png")
        print("  Or use --custom-refs with local references in: references/")
        return False

    # Load reference images
    left_ref = load_image(left_ref_path)
    right_ref = load_image(right_ref_path)

    if not left_ref or not right_ref:
        print("Error: Could not load reference images.")
        return False

    # Load prompts
    left_prompt = extract_veo_prompt(PROMPTS_DIR / "07_left_developer.md")
    right_prompt = extract_veo_prompt(PROMPTS_DIR / "07_right_grandmother.md")

    if not left_prompt or not right_prompt:
        print("Error: Could not extract prompts from markdown files")
        return False

    # Generate videos
    left_ok = generate_video(
        client, left_prompt,
        OUTPUTS_DIR / "07_left_developer.mp4",
        reference_image=left_ref
    )

    right_ok = generate_video(
        client, right_prompt,
        OUTPUTS_DIR / "07_right_grandmother.mp4",
        reference_image=right_ref
    )

    return left_ok and right_ok


def composite_with_sepia():
    """Composite left/right videos with sepia effect."""
    print("\n=== Compositing with Sepia Effect ===")
    COMPOSITED_DIR.mkdir(exist_ok=True)

    left_path = OUTPUTS_DIR / "07_left_developer.mp4"
    right_path = OUTPUTS_DIR / "07_right_grandmother.mp4"
    output_path = COMPOSITED_DIR / "07_split_screen_sepia.mp4"

    if not left_path.exists() or not right_path.exists():
        print("Error: Source videos not found. Run with --generate-videos first.")
        return False

    # FFmpeg filter:
    # 1. Stack videos side by side
    # 2. Add white divider line
    # 3. Apply sepia effect (desaturate + sepia tone)
    # 4. Add vignette
    # 5. Letterbox to 16:9 (ensure even width for libx264)
    filter_complex = (
        # Stack horizontally
        "[0:v][1:v]hstack=inputs=2[stacked];"
        # Add white divider line
        "[stacked]drawbox=x=(iw/2)-1:y=0:w=2:h=ih:color=white:t=fill[lined];"
        # Apply sepia effect: desaturate then colorize
        "[lined]colorchannelmixer=.393:.769:.189:0:.349:.686:.168:0:.272:.534:.131[sepia];"
        # Add slight vignette
        "[sepia]vignette=PI/4[vignetted];"
        # Letterbox to 16:9 (ceil to even width for h264 compatibility)
        "[vignetted]pad=w=ceil(ih*16/9/2)*2:h=ih:x=(ow-iw)/2:y=0:color=black[out]"
    )

    cmd = [
        "ffmpeg", "-y",
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

    print(f"Compositing: {output_path.name}")
    try:
        result = subprocess.run(cmd, capture_output=True, text=True)
        if result.returncode != 0:
            print(f"Error: {result.stderr[:500]}")
            return False
        print(f"Created: {output_path}")
        return True
    except Exception as e:
        print(f"Error: {e}")
        return False


def main():
    parser = argparse.ArgumentParser(
        description="Generate segment 07 split screen sepia",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    # Generate videos using cold open frames (default, recommended):
    python generate_segment_07.py --generate-videos

    # Generate videos using custom local reference images:
    python generate_segment_07.py --generate-videos --custom-refs

    # Composite only (videos must already exist):
    python generate_segment_07.py --composite

    # Do everything:
    python generate_segment_07.py --all
"""
    )
    parser.add_argument("--generate-videos", action="store_true",
                        help="Generate videos using reference frames")
    parser.add_argument("--composite", action="store_true",
                        help="Composite with sepia effect")
    parser.add_argument("--custom-refs", action="store_true",
                        help="Use local references/ instead of cold open frames")
    parser.add_argument("--all", action="store_true",
                        help="Generate videos and composite")
    args = parser.parse_args()

    if args.all:
        args.generate_videos = True
        args.composite = True

    if not any([args.generate_videos, args.composite]):
        parser.print_help()
        return

    client = None
    if args.generate_videos:
        client = get_client()
        generate_videos(client, use_custom_refs=args.custom_refs)

    if args.composite:
        composite_with_sepia()

    print("\n=== Done ===")


if __name__ == "__main__":
    main()
