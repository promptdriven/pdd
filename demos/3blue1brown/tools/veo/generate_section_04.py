#!/usr/bin/env python3
"""
Generate Veo 3.1 video segments for 04-precision-tradeoff.

Generates all 4 videos in parallel:
- 01_split_3d_vs_mold_left.mp4 (3D printer side)
- 01_split_3d_vs_mold_right.mp4 (injection mold side)
- 02_3d_printer_focus.mp4 (closeup for hybrid)
- 03_mold_flow_focus.mp4 (closeup for hybrid)

Usage:
    python generate_section_04.py --generate           # Generate all in parallel
    python generate_section_04.py --generate --segment 01  # Generate segment 01 only
    python generate_section_04.py --dry-run            # Print prompts without generating
    python generate_section_04.py --composite          # Composite split-screen after generation
"""

import argparse
import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
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
SPECS_DIR = PROJECT_ROOT / "specs" / "04-precision-tradeoff"
OUTPUTS_DIR = PROJECT_ROOT / "outputs" / "veo" / "04-precision-tradeoff" / "raw"
COMPOSITE_DIR = PROJECT_ROOT / "outputs" / "veo" / "04-precision-tradeoff" / "composited"

# Vertex AI settings
DEFAULT_PROJECT = "prompt-driven-development"
DEFAULT_LOCATION = "us-central1"

# Video generation jobs
JOBS = {
    "01_left": {
        "spec": "01_split_3d_vs_mold.md",
        "output": "01_split_3d_vs_mold_left.mp4",
        "aspect_ratio": "9:16",
        "description": "3D printer (left side of split)",
        "prompt_section": "LEFT SIDE",
    },
    "01_right": {
        "spec": "01_split_3d_vs_mold.md",
        "output": "01_split_3d_vs_mold_right.mp4",
        "aspect_ratio": "9:16",
        "description": "Injection mold (right side of split)",
        "prompt_section": "RIGHT SIDE",
    },
    "02": {
        "spec": "02_3d_printer_focus.md",
        "output": "02_3d_printer_focus.mp4",
        "aspect_ratio": "16:9",
        "description": "3D printer closeup (hybrid base)",
        "prompt_section": "Option B",
    },
    "03": {
        "spec": "03_mold_flow_focus.md",
        "output": "03_mold_flow_focus.mp4",
        "aspect_ratio": "16:9",
        "description": "Mold flow closeup (hybrid base)",
        "prompt_section": "Option B",
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


def extract_veo_prompt(md_path: Path, section_hint: str = None) -> str:
    """Extract Veo prompt from markdown file.

    Args:
        md_path: Path to markdown spec file
        section_hint: Optional hint to find specific section (e.g., "LEFT SIDE", "Option B")

    Returns:
        Extracted prompt text
    """
    content = md_path.read_text()

    # For split-screen, extract left or right section
    if section_hint == "LEFT SIDE":
        # Look for LEFT SIDE section in the Veo prompt
        match = re.search(r"LEFT SIDE:\s*(.*?)(?:RIGHT SIDE:|COMPOSITION:|$)", content, re.DOTALL | re.IGNORECASE)
        if match:
            prompt = match.group(1).strip()
            # Clean up markdown formatting
            prompt = re.sub(r"^- ", "", prompt, flags=re.MULTILINE)
            prompt = prompt.replace("\n- ", "\n")
            # Add common elements
            prompt += "\n\nVertical 9:16 portrait framing.\nCinematic, photorealistic, 4K.\nDark background, well-lit subject.\nNO PEOPLE.\nNO TEXT OVERLAY.\nDURATION: 15 seconds."
            return prompt

    elif section_hint == "RIGHT SIDE":
        match = re.search(r"RIGHT SIDE:\s*(.*?)(?:COMPOSITION:|ATMOSPHERE:|$)", content, re.DOTALL | re.IGNORECASE)
        if match:
            prompt = match.group(1).strip()
            prompt = re.sub(r"^- ", "", prompt, flags=re.MULTILINE)
            prompt = prompt.replace("\n- ", "\n")
            prompt += "\n\nVertical 9:16 portrait framing.\nCinematic, photorealistic, 4K.\nDark background, well-lit subject.\nNO PEOPLE.\nNO TEXT OVERLAY.\nDURATION: 15 seconds."
            return prompt

    elif section_hint == "Option B":
        # Look for Option B section with its own Veo prompt
        match = re.search(r"### Option B.*?```\s*(.*?)\s*```", content, re.DOTALL)
        if match:
            return match.group(1).strip()

    # Default: extract main Veo prompt
    pattern = r"##[#]?\s+Veo[\s\d.]*Prompt\s*```\s*(.*?)\s*```"
    match = re.search(pattern, content, re.DOTALL)
    return match.group(1).strip() if match else ""


def generate_video(client, job_id: str, job: dict) -> tuple[str, bool, str]:
    """Generate a single video.

    Returns:
        Tuple of (job_id, success, message)
    """
    spec_path = SPECS_DIR / job["spec"]
    output_path = OUTPUTS_DIR / job["output"]

    prompt = extract_veo_prompt(spec_path, job.get("prompt_section"))
    if not prompt:
        return (job_id, False, f"Could not extract prompt from {spec_path}")

    print(f"\n[{job_id}] Generating: {job['description']}")
    print(f"  Output: {output_path.name}")
    print(f"  Aspect: {job['aspect_ratio']}")
    print(f"  Prompt: {prompt[:100]}...")

    try:
        gen_kwargs = {
            "model": "veo-3.1-generate-preview",
            "prompt": prompt,
            "config": types.GenerateVideosConfig(
                aspect_ratio=job["aspect_ratio"],
                number_of_videos=1,
            ),
        }

        operation = client.models.generate_videos(**gen_kwargs)
        print(f"  [{job_id}] Operation started: {operation.name}")

        elapsed = 0
        while not operation.done:
            time.sleep(20)
            elapsed += 20
            print(f"  [{job_id}] Waiting... ({elapsed}s)")
            operation = client.operations.get(operation)
            if elapsed > 600:
                return (job_id, False, "Timeout after 600s")

        if operation.error:
            return (job_id, False, f"API error: {operation.error}")

        if operation.response and operation.response.generated_videos:
            video = operation.response.generated_videos[0].video
            if hasattr(video, 'video_bytes') and video.video_bytes:
                with open(output_path, "wb") as f:
                    f.write(video.video_bytes)
                return (job_id, True, f"Saved: {output_path}")

        return (job_id, False, "No video in response")

    except Exception as e:
        return (job_id, False, f"Exception: {e}")


def composite_split_screen():
    """Composite left and right videos into split-screen."""
    left_path = OUTPUTS_DIR / "01_split_3d_vs_mold_left.mp4"
    right_path = OUTPUTS_DIR / "01_split_3d_vs_mold_right.mp4"
    output_path = COMPOSITE_DIR / "01_split_3d_vs_mold.mp4"

    print(f"\nCompositing split-screen...")
    print(f"  Left:  {left_path.name}")
    print(f"  Right: {right_path.name}")

    if not left_path.exists():
        print(f"  Error: Left video not found")
        return False
    if not right_path.exists():
        print(f"  Error: Right video not found")
        return False

    COMPOSITE_DIR.mkdir(parents=True, exist_ok=True)

    # 9:16 videos stacked side by side with white divider
    filter_complex = (
        "[0:v][1:v]hstack=inputs=2[stacked];"
        "[stacked]drawbox=x=(iw/2)-1:y=0:w=2:h=ih:color=white:t=fill[lined];"
        "[lined]pad=w=ih*16/9:h=ih:x=(ow-iw)/2:y=0:color=black[out]"
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

    try:
        result = subprocess.run(cmd, capture_output=True, text=True)
        if result.returncode != 0:
            print(f"  Error: ffmpeg failed: {result.stderr[:200]}")
            return False
        print(f"  Created: {output_path}")
        return True
    except Exception as e:
        print(f"  Error: {e}")
        return False


def main():
    parser = argparse.ArgumentParser(
        description="Generate Veo segments for 04-precision-tradeoff",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--generate", action="store_true",
                        help="Generate videos (in parallel by default)")
    parser.add_argument("--segment", type=str,
                        help="Generate only this segment (01, 02, or 03)")
    parser.add_argument("--dry-run", action="store_true",
                        help="Print prompts without generating")
    parser.add_argument("--composite", action="store_true",
                        help="Composite split-screen after generation")
    parser.add_argument("--sequential", action="store_true",
                        help="Generate sequentially instead of in parallel")
    args = parser.parse_args()

    if not any([args.generate, args.dry_run, args.composite]):
        parser.print_help()
        return

    # Determine which jobs to run
    if args.segment:
        if args.segment == "01":
            jobs_to_run = {k: v for k, v in JOBS.items() if k.startswith("01")}
        else:
            jobs_to_run = {args.segment: JOBS[args.segment]}
    else:
        jobs_to_run = JOBS

    # Dry run - just print prompts
    if args.dry_run:
        for job_id, job in jobs_to_run.items():
            spec_path = SPECS_DIR / job["spec"]
            prompt = extract_veo_prompt(spec_path, job.get("prompt_section"))
            print(f"\n{'='*60}")
            print(f"[{job_id}] {job['description']}")
            print(f"Aspect: {job['aspect_ratio']}")
            print(f"{'='*60}")
            print(prompt or "ERROR: Could not extract prompt")
        return

    # Generate videos
    if args.generate:
        OUTPUTS_DIR.mkdir(parents=True, exist_ok=True)
        client = get_client()

        print(f"\n{'='*60}")
        print(f"Generating {len(jobs_to_run)} videos {'sequentially' if args.sequential else 'in parallel'}...")
        print(f"{'='*60}")

        results = {}

        if args.sequential:
            for job_id, job in jobs_to_run.items():
                job_id, success, msg = generate_video(client, job_id, job)
                results[job_id] = (success, msg)
        else:
            with ThreadPoolExecutor(max_workers=4) as executor:
                futures = {
                    executor.submit(generate_video, client, job_id, job): job_id
                    for job_id, job in jobs_to_run.items()
                }
                for future in as_completed(futures):
                    job_id, success, msg = future.result()
                    results[job_id] = (success, msg)
                    print(f"\n[{job_id}] {'SUCCESS' if success else 'FAILED'}: {msg}")

        # Summary
        print(f"\n{'='*60}")
        print("Generation Summary")
        print(f"{'='*60}")
        for job_id, (success, msg) in results.items():
            status = "OK" if success else "FAILED"
            print(f"  {job_id}: {status}")

        succeeded = sum(1 for s, _ in results.values() if s)
        print(f"\n  Total: {succeeded}/{len(results)} succeeded")

        # Composite if all split-screen parts succeeded
        if args.composite or (succeeded == len(results) and "01_left" in results and "01_right" in results):
            composite_split_screen()

    # Composite only
    elif args.composite:
        composite_split_screen()


if __name__ == "__main__":
    main()
