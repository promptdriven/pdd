#!/usr/bin/env python3
"""
Generate segment 09 (patch cycle) for section 02.

Developer resignation and patching continues. Uses the last frame from
segment 08 as reference for character consistency.

Usage:
    python generate_segment_09.py --generate  # Generate video
    python generate_segment_09.py --extract-ref  # Extract reference frame from seg 08
    python generate_segment_09.py --all  # Do everything
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
PROJECT_ROOT = SCRIPT_DIR.parent.parent
PROMPTS_DIR = PROJECT_ROOT / "specs" / "01-economics" / "prompts"
OUTPUTS_DIR = PROJECT_ROOT / "outputs" / "veo" / "01-economics" / "raw"
FRAMES_DIR = PROJECT_ROOT / "outputs" / "veo" / "01-economics" / "frames"

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


def extract_last_frame(video_path: Path, output_path: Path) -> bool:
    """Extract the last frame from a video using ffmpeg."""
    print(f"\nExtracting last frame from: {video_path.name}")

    if not video_path.exists():
        print(f"  ERROR: Video not found: {video_path}")
        return False

    try:
        # Get video duration
        probe_cmd = [
            "ffprobe", "-v", "error",
            "-show_entries", "format=duration",
            "-of", "default=noprint_wrappers=1:nokey=1",
            str(video_path)
        ]
        result = subprocess.run(probe_cmd, capture_output=True, text=True)
        duration = float(result.stdout.strip())
        print(f"  Duration: {duration}s")

        # Extract frame at duration - 0.1 seconds
        extract_cmd = [
            "ffmpeg", "-y",
            "-ss", str(max(0, duration - 0.1)),
            "-i", str(video_path),
            "-vframes", "1",
            "-q:v", "2",
            str(output_path)
        ]
        subprocess.run(extract_cmd, capture_output=True, check=True)

        if output_path.exists():
            print(f"  Saved: {output_path}")
            return True
        return False
    except Exception as e:
        print(f"  Error: {e}")
        return False


def load_image(path: Path):
    """Load image for Veo input."""
    if not path.exists():
        print(f"  ERROR: Image not found: {path}")
        return None
    with open(path, "rb") as f:
        return types.Image(image_bytes=f.read(), mime_type="image/png")


def generate_video(client, prompt: str, output_path: Path, reference_image=None, aspect_ratio="16:9"):
    """Generate a video using Veo."""
    print(f"\nGenerating: {output_path.name}")
    print(f"  Aspect ratio: {aspect_ratio}")
    print(f"  Prompt: {prompt[:80]}...")

    try:
        gen_kwargs = {
            "model": "veo-3.1-generate-preview",
            "prompt": prompt,
            "config": types.GenerateVideosConfig(
                aspect_ratio=aspect_ratio,
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


def extract_reference_frame():
    """Extract reference frame from segment 08 video."""
    print("\n=== Extracting Reference Frame ===")
    FRAMES_DIR.mkdir(exist_ok=True)

    seg08_video = OUTPUTS_DIR / "08_developer_edit_complete.mp4"
    ref_frame = FRAMES_DIR / "08_developer_last.png"

    return extract_last_frame(seg08_video, ref_frame)


def generate_segment(client):
    """Generate segment 09 video."""
    print("\n=== Generating Segment 09 ===")
    OUTPUTS_DIR.mkdir(exist_ok=True)

    # Reference frame from segment 08
    ref_frame_path = FRAMES_DIR / "08_developer_last.png"

    if not ref_frame_path.exists():
        print(f"ERROR: Reference frame not found: {ref_frame_path}")
        print("  Run with --extract-ref first, or --all")
        return False

    ref_image = load_image(ref_frame_path)
    if not ref_image:
        return False

    # Load prompt
    prompt_path = PROMPTS_DIR / "09_patch_cycle.md"
    prompt = extract_veo_prompt(prompt_path)

    if not prompt:
        print(f"ERROR: Could not extract prompt from {prompt_path}")
        return False

    # Generate video (16:9 horizontal)
    output_path = OUTPUTS_DIR / "09_patch_cycle.mp4"
    return generate_video(client, prompt, output_path, reference_image=ref_image, aspect_ratio="16:9")


def main():
    parser = argparse.ArgumentParser(
        description="Generate segment 09 (patch cycle)",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    # Extract reference frame from segment 08:
    python generate_segment_09.py --extract-ref

    # Generate video (requires reference frame):
    python generate_segment_09.py --generate

    # Do everything:
    python generate_segment_09.py --all
"""
    )
    parser.add_argument("--extract-ref", action="store_true",
                        help="Extract reference frame from segment 08")
    parser.add_argument("--generate", action="store_true",
                        help="Generate video using reference frame")
    parser.add_argument("--all", action="store_true",
                        help="Extract reference and generate video")
    args = parser.parse_args()

    if args.all:
        args.extract_ref = True
        args.generate = True

    if not any([args.extract_ref, args.generate]):
        parser.print_help()
        return

    if args.extract_ref:
        extract_reference_frame()

    if args.generate:
        client = get_client()
        generate_segment(client)

    print("\n=== Done ===")


if __name__ == "__main__":
    main()
