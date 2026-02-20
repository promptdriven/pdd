#!/usr/bin/env python3
"""Generate reference images for character consistency in Veo video segments.

Uses Imagen 3.0 to create consistent character reference images that are then
fed to Veo for image-to-video generation.

Usage:
    python generate_references.py                       # Generate all references
    python generate_references.py --section cold_open   # Section-specific references

Requires: GOOGLE_APPLICATION_CREDENTIALS or GOOGLE_API_KEY environment variable.
"""

import argparse
import json
import os
import sys
from pathlib import Path

try:
    from google import genai
    from google.genai import types
except ImportError:
    print('{"step":"veo","progress":-1,"message":"google-genai not installed. Run: pip install google-genai","status":"error"}', flush=True)
    sys.exit(1)

from utils import (
    PROJECT_ROOT, VEO_OUTPUT_DIR, load_project_config,
    emit_progress, emit_error, emit_done,
)

DEFAULT_PROJECT = "prompt-driven-development"
DEFAULT_LOCATION = "us-central1"


def get_client(use_api_key: bool = False) -> genai.Client:
    """Initialize and return a Google GenAI client."""
    if use_api_key:
        api_key = os.environ.get("GOOGLE_API_KEY")
        if not api_key:
            emit_error("veo", "GOOGLE_API_KEY environment variable not set")
            sys.exit(1)
        return genai.Client(api_key=api_key)

    creds_path = os.environ.get("GOOGLE_APPLICATION_CREDENTIALS")
    if not creds_path:
        emit_error("veo", "GOOGLE_APPLICATION_CREDENTIALS not set. Use --api-key flag for API key auth.")
        sys.exit(1)

    project = DEFAULT_PROJECT
    try:
        with open(creds_path) as f:
            project = json.load(f).get("project_id", DEFAULT_PROJECT)
    except Exception:
        pass

    return genai.Client(vertexai=True, project=project, location=DEFAULT_LOCATION)


def generate_image(client: genai.Client, prompt: str, output_path: Path, aspect_ratio: str = "9:16") -> bool:
    """Generate an image using Imagen 3.0 and save it."""
    try:
        response = client.models.generate_images(
            model="imagen-3.0-generate-002",
            prompt=prompt,
            config=types.GenerateImagesConfig(
                number_of_images=1,
                aspect_ratio=aspect_ratio,
                person_generation="allow_adult",
            ),
        )

        if not response.generated_images:
            return False

        image = response.generated_images[0].image
        if hasattr(image, "image_bytes") and image.image_bytes:
            with open(output_path, "wb") as f:
                f.write(image.image_bytes)
            return True

        image.save(str(output_path))
        return True

    except Exception as e:
        emit_progress("veo", -1, f"Image generation error: {e}")
        return False


def main():
    parser = argparse.ArgumentParser(description="Generate reference images for Veo")
    parser.add_argument("--section", help="Section ID (default: generate project-wide references)")
    parser.add_argument("--api-key", action="store_true", help="Use GOOGLE_API_KEY instead of Vertex AI")
    args = parser.parse_args()

    config = load_project_config()
    veo_config = config.get("veo", {})
    references = veo_config.get("references", [])

    if not references:
        emit_done("veo", "No reference images configured in project.json veo.references")
        return

    client = get_client(use_api_key=args.api_key)
    refs_dir = PROJECT_ROOT / ".." / "references"
    refs_dir.mkdir(parents=True, exist_ok=True)

    results = {}
    total = len(references)

    for i, ref in enumerate(references):
        name = ref.get("name", f"reference_{i}")
        prompt = ref.get("prompt", "")
        aspect = ref.get("aspectRatio", "9:16")
        subdir = ref.get("subdir", "")

        if not prompt:
            continue

        output_dir = refs_dir / subdir if subdir else refs_dir
        output_dir.mkdir(parents=True, exist_ok=True)
        output_path = output_dir / f"{name}.png"

        pct = int(10 + 80 * (i / total))
        emit_progress("veo", pct, f"Generating reference: {name}")
        results[name] = generate_image(client, prompt, output_path, aspect)

    succeeded = sum(1 for s in results.values() if s)
    if succeeded == total:
        emit_done("veo", f"Generated {total} reference image(s)")
    else:
        emit_error("veo", f"{succeeded}/{total} reference images generated")
        sys.exit(1)


if __name__ == "__main__":
    main()
