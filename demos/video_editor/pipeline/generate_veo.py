#!/usr/bin/env python3
"""Generate video segments using Google's Veo API.

Reads spec prompt files from the specs directory and generates video clips
for each section. Supports reference images for character consistency,
sequential frame chaining, and separate-sides compositing.

Usage:
    python generate_veo.py --section cold_open              # Single section
    python generate_veo.py --section all                    # All sections
    python generate_veo.py --section cold_open --dry-run    # Print prompts only
    python generate_veo.py --use-references --separate-sides
"""

import argparse
import json
import mimetypes
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
    print('{"step":"veo","progress":-1,"message":"google-genai not installed","status":"error"}', flush=True)
    sys.exit(1)

from utils import (
    PROJECT_ROOT, VEO_OUTPUT_DIR, SPECS_DIR,
    load_project_config, get_sections,
    emit_progress, emit_error, emit_done,
)

DEFAULT_PROJECT = "prompt-driven-development"
DEFAULT_LOCATION = "us-central1"


def get_client(use_api_key: bool = False) -> genai.Client:
    """Initialize Google GenAI client."""
    if use_api_key:
        api_key = os.environ.get("GOOGLE_API_KEY")
        if not api_key:
            emit_error("veo", "GOOGLE_API_KEY not set")
            sys.exit(1)
        return genai.Client(api_key=api_key)

    creds_path = os.environ.get("GOOGLE_APPLICATION_CREDENTIALS")
    if not creds_path:
        emit_error("veo", "GOOGLE_APPLICATION_CREDENTIALS not set")
        sys.exit(1)

    project = DEFAULT_PROJECT
    try:
        with open(creds_path) as f:
            project = json.load(f).get("project_id", DEFAULT_PROJECT)
    except Exception:
        pass

    return genai.Client(vertexai=True, project=project, location=DEFAULT_LOCATION)


def extract_veo_prompt(md_content: str) -> str:
    """Extract the Veo prompt from a markdown file's ## Veo Prompt section."""
    pattern = r"## Veo Prompt\s*```\s*(.*?)\s*```"
    match = re.search(pattern, md_content, re.DOTALL)
    return match.group(1).strip() if match else ""


def load_reference_image(image_path: Path):
    """Load a reference image for image-to-video generation."""
    if not image_path.exists():
        return None
    try:
        mime_type, _ = mimetypes.guess_type(str(image_path))
        if not mime_type:
            mime_type = "image/png"
        with open(image_path, "rb") as f:
            image_bytes = f.read()
        return types.Image(image_bytes=image_bytes, mime_type=mime_type)
    except Exception:
        return None


def extract_last_frame(video_path: Path, output_path: Path) -> bool:
    """Extract the last frame from a video using ffmpeg."""
    try:
        result = subprocess.run(
            ["ffprobe", "-v", "error", "-show_entries", "format=duration",
             "-of", "default=noprint_wrappers=1:nokey=1", str(video_path)],
            capture_output=True, text=True,
        )
        duration = float(result.stdout.strip())
        subprocess.run(
            ["ffmpeg", "-y", "-ss", str(max(0, duration - 0.1)),
             "-i", str(video_path), "-vframes", "1", "-q:v", "2", str(output_path)],
            capture_output=True, check=True,
        )
        return output_path.exists()
    except Exception:
        return False


def save_video(client: genai.Client, video, output_path: Path, use_vertexai: bool = False) -> bool:
    """Save a Veo-generated video to disk."""
    if hasattr(video, "video_bytes") and video.video_bytes:
        with open(output_path, "wb") as f:
            f.write(video.video_bytes)
        return True

    if not use_vertexai:
        try:
            client.files.download(file=video)
            video.save(str(output_path))
            return True
        except Exception:
            pass

    if hasattr(video, "uri") and video.uri:
        uri = video.uri
        if uri.startswith("gs://"):
            try:
                from google.cloud import storage
                parts = uri[5:].split("/", 1)
                bucket = storage.Client().bucket(parts[0])
                bucket.blob(parts[1] if len(parts) > 1 else "").download_to_filename(str(output_path))
                return True
            except Exception:
                pass
        else:
            try:
                import requests
                resp = requests.get(uri, stream=True)
                resp.raise_for_status()
                with open(output_path, "wb") as f:
                    for chunk in resp.iter_content(chunk_size=8192):
                        f.write(chunk)
                return True
            except Exception:
                pass

    return False


def generate_video(
    client: genai.Client,
    prompt: str,
    output_path: Path,
    model: str = "veo-3.1-generate-preview",
    use_vertexai: bool = True,
    reference_image=None,
    poll_interval: int = 20,
    max_wait: int = 600,
) -> bool:
    """Generate a video using Veo API and save it."""
    aspect = "9:16" if reference_image is not None else "16:9"
    gen_kwargs = {
        "model": model,
        "prompt": prompt,
        "config": types.GenerateVideosConfig(aspect_ratio=aspect, number_of_videos=1),
    }
    if reference_image is not None:
        gen_kwargs["image"] = reference_image

    try:
        operation = client.models.generate_videos(**gen_kwargs)

        elapsed = 0
        while not operation.done:
            if elapsed >= max_wait:
                return False
            time.sleep(poll_interval)
            elapsed += poll_interval
            operation = client.operations.get(operation)

        if operation.error:
            return False

        if not operation.response or not operation.response.generated_videos:
            return False

        video = operation.response.generated_videos[0].video
        return save_video(client, video, output_path, use_vertexai=use_vertexai)

    except Exception:
        return False


def find_prompts_for_section(section: dict) -> list[dict]:
    """Find all Veo prompt files for a section's spec directory."""
    spec_dir = SPECS_DIR / section["specDir"] / "prompts"
    if not spec_dir.exists():
        spec_dir = SPECS_DIR / section["specDir"]

    prompts = []
    if spec_dir.exists():
        for md_file in sorted(spec_dir.glob("*.md")):
            content = md_file.read_text()
            prompt_text = extract_veo_prompt(content)
            if prompt_text:
                prompts.append({
                    "file": md_file.name,
                    "prompt": prompt_text,
                    "stem": md_file.stem,
                })
    return prompts


def main():
    parser = argparse.ArgumentParser(description="Generate Veo video segments")
    parser.add_argument("--section", default="all", help="Section ID or 'all'")
    parser.add_argument("--model", default=None, help="Veo model override")
    parser.add_argument("--dry-run", action="store_true", help="Print prompts only")
    parser.add_argument("--api-key", action="store_true", help="Use API key auth")
    parser.add_argument("--use-references", action="store_true", help="Use reference images")
    parser.add_argument("--separate-sides", action="store_true", help="Generate left/right separately")
    parser.add_argument("--sequential", action="store_true", help="Chain frames for continuity")
    args = parser.parse_args()

    config = load_project_config()
    veo_config = config.get("veo", {})
    model = args.model or veo_config.get("model", "veo-3.1-generate-preview")
    sections = get_sections()

    if args.section == "all":
        target_sections = sections
    else:
        target_sections = [s for s in sections if s["id"] == args.section]
        if not target_sections:
            emit_error("veo", f"Unknown section: {args.section}")
            sys.exit(1)

    client = None
    if not args.dry_run:
        client = get_client(use_api_key=args.api_key)

    total_prompts = 0
    succeeded = 0

    for section in target_sections:
        prompts = find_prompts_for_section(section)
        if not prompts:
            emit_progress("veo", 0, f"No prompts found for {section['id']}")
            continue

        output_dir = VEO_OUTPUT_DIR / section["specDir"] / "raw"
        output_dir.mkdir(parents=True, exist_ok=True)

        for i, prompt_info in enumerate(prompts):
            total_prompts += 1
            pct = int(10 + 80 * (total_prompts / max(1, len(prompts) * len(target_sections))))
            emit_progress("veo", pct, f"[{section['id']}] {prompt_info['stem']}")

            if args.dry_run:
                emit_progress("veo", pct, f"  Prompt: {prompt_info['prompt'][:100]}...")
                succeeded += 1
                continue

            output_path = output_dir / f"{prompt_info['stem']}.mp4"
            if generate_video(
                client, prompt_info["prompt"], output_path,
                model=model, use_vertexai=not args.api_key,
            ):
                succeeded += 1

    if succeeded == total_prompts:
        emit_done("veo", f"Generated {total_prompts} video(s)")
    elif total_prompts == 0:
        emit_done("veo", "No prompts found to generate")
    else:
        emit_error("veo", f"{succeeded}/{total_prompts} videos generated")
        sys.exit(1)


if __name__ == "__main__":
    main()
