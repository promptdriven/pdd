#!/usr/bin/env python3
"""
Generate Veo 3.1 video segments for 02-paradigm-shift.

Supports segments: 01, 02, 04, 05, 07

Usage:
    python generate_paradigm_shift.py --segment 02 --generate
    python generate_paradigm_shift.py --segment 04 --generate
    python generate_paradigm_shift.py --segment 05 --generate
    python generate_paradigm_shift.py --segment 07 --generate
    python generate_paradigm_shift.py --segment 02 --dry-run
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
SPECS_DIR = PROJECT_ROOT / "specs" / "02-paradigm-shift"
OUTPUTS_DIR = PROJECT_ROOT / "outputs" / "veo" / "02-paradigm-shift" / "raw"

# Vertex AI settings
DEFAULT_PROJECT = "prompt-driven-development"
DEFAULT_LOCATION = "us-central1"

# Segment definitions
SEGMENTS = {
    "01": {
        "spec": "01_factory_floor.md",
        "output": "01_factory_floor.mp4",
        "aspect_ratio": "16:9",
        "description": "Factory floor establishing shot",
    },
    "02": {
        "spec": "02_mold_closeup.md",
        "output": "02_mold_closeup.mp4",
        "aspect_ratio": "16:9",
        "description": "Mold close-up with liquid plastic",
    },
    "04": {
        "spec": "04_defect_discovered.md",
        "output": "04_defect_discovered.mp4",
        "aspect_ratio": "16:9",
        "description": "Defective plastic part close-up",
    },
    "05": {
        "spec": "05_engineer_fixes_mold.md",
        "output": "05_engineer_fixes_mold.mp4",
        "aspect_ratio": "16:9",
        "description": "Engineer adjusting the mold",
    },
    "07": {
        "spec": "07_craftsman_vs_mold.md",
        "output": "07_craftsman_vs_mold.mp4",
        "aspect_ratio": "16:9",
        "description": "Split screen: craftsman vs injection mold",
    },
}


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

    Handles headers like '## Veo Prompt', '## Veo 3.1 Prompt',
    and '### Veo 3.1 Prompt'.
    """
    content = md_path.read_text()
    pattern = r"##[#]?\s+Veo[\s\d.]*Prompt\s*```\s*(.*?)\s*```"
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


def main():
    parser = argparse.ArgumentParser(
        description="Generate Veo segments for 02-paradigm-shift",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--segment", required=True, choices=list(SEGMENTS.keys()),
                        help="Segment to generate")
    parser.add_argument("--generate", action="store_true",
                        help="Generate video")
    parser.add_argument("--dry-run", action="store_true",
                        help="Print prompt without generating")
    args = parser.parse_args()

    if not any([args.generate, args.dry_run]):
        parser.print_help()
        return

    seg = SEGMENTS[args.segment]
    spec_path = SPECS_DIR / seg["spec"]
    print(f"\n=== Segment {args.segment}: {seg['description']} ===")

    prompt = extract_veo_prompt(spec_path)
    if not prompt:
        print(f"ERROR: Could not extract prompt from {spec_path}")
        sys.exit(1)

    if args.dry_run:
        print(f"\n{prompt}")
        return

    OUTPUTS_DIR.mkdir(parents=True, exist_ok=True)
    client = get_client()
    output_path = OUTPUTS_DIR / seg["output"]
    success = generate_video(client, prompt, output_path, aspect_ratio=seg["aspect_ratio"])

    if success:
        print("\n=== Done ===")
    else:
        print("\n=== Failed ===")
        sys.exit(1)


if __name__ == "__main__":
    main()
