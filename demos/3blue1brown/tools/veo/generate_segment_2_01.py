#!/usr/bin/env python3
"""
Generate segment 2.01 (factory floor establishing shot) for section 02-paradigm-shift.

Single wide shot of an injection molding machine on a factory floor.
No people, no split screen, no reference images needed.

Usage:
    python generate_segment_2_01.py --generate   # Generate video
    python generate_segment_2_01.py --dry-run    # Print prompt without generating
"""

import argparse
import json
import os
import re
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
SPEC_PATH = PROJECT_ROOT / "specs" / "02-paradigm-shift" / "01_factory_floor.md"
OUTPUTS_DIR = PROJECT_ROOT / "outputs" / "veo" / "02-paradigm-shift" / "raw"

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
    """Extract Veo prompt from markdown file.

    Handles both '## Veo Prompt' and '## Veo 3.1 Prompt' headers.
    """
    content = md_path.read_text()
    pattern = r"## Veo[\s\d.]*Prompt\s*```\s*(.*?)\s*```"
    match = re.search(pattern, content, re.DOTALL)
    return match.group(1).strip() if match else ""


def generate_video(client, prompt: str, output_path: Path, aspect_ratio="16:9"):
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


def generate_segment(client):
    """Generate the factory floor establishing shot."""
    print("\n=== Generating Segment 2.01: Factory Floor ===")
    OUTPUTS_DIR.mkdir(parents=True, exist_ok=True)

    # Load prompt from spec
    prompt = extract_veo_prompt(SPEC_PATH)
    if not prompt:
        print(f"ERROR: Could not extract prompt from {SPEC_PATH}")
        return False

    # Generate video (16:9 wide establishing shot)
    output_path = OUTPUTS_DIR / "01_factory_floor.mp4"
    return generate_video(client, prompt, output_path, aspect_ratio="16:9")


def main():
    parser = argparse.ArgumentParser(
        description="Generate segment 2.01 (factory floor establishing shot)",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    # Generate video:
    python generate_segment_2_01.py --generate

    # Dry run (print prompt only):
    python generate_segment_2_01.py --dry-run
"""
    )
    parser.add_argument("--generate", action="store_true",
                        help="Generate video")
    parser.add_argument("--dry-run", action="store_true",
                        help="Print prompt without generating")
    args = parser.parse_args()

    if not any([args.generate, args.dry_run]):
        parser.print_help()
        return

    if args.dry_run:
        prompt = extract_veo_prompt(SPEC_PATH)
        if prompt:
            print(f"\n=== Veo Prompt ===\n{prompt}")
        else:
            print(f"ERROR: Could not extract prompt from {SPEC_PATH}")
        return

    if args.generate:
        client = get_client()
        success = generate_segment(client)
        if success:
            print("\n=== Done ===")
        else:
            print("\n=== Failed ===")
            sys.exit(1)


if __name__ == "__main__":
    main()
