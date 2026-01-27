#!/usr/bin/env python3
"""
Generate video segments for the 3Blue1Brown cold open using Google's Veo API.

Usage:
    python generate_segments.py [--segment SEGMENT_ID] [--separate-sides] [--model MODEL]

Examples:
    python generate_segments.py                      # Generate all segments (Vertex AI)
    python generate_segments.py --segment 01a        # Generate only segment 01a
    python generate_segments.py --separate-sides     # Generate left/right sides separately
    python generate_segments.py --use-references     # Use reference images for consistency
    python generate_segments.py --api-key            # Use API key instead of Vertex AI

Character Consistency:
    For consistent characters across segments, first generate reference images:
        python generate_references.py
    Then generate videos with references:
        python generate_segments.py --use-references --separate-sides

Vertex AI Authentication:
    Set GOOGLE_APPLICATION_CREDENTIALS to your service account JSON file path.
    The script uses project 'prompt-driven-development' and location 'us-central1' by default.
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

# Default Vertex AI settings
DEFAULT_PROJECT = "prompt-driven-development"
DEFAULT_LOCATION = "us-central1"

# Reference image paths (relative to script directory)
REFERENCE_IMAGES = {
    "left": "references/developer_reference.png",
    "right": "references/grandmother_reference.png",
}

# Segment definitions with durations
SEGMENTS = {
    "01a": {
        "name": "establish_split_screen",
        "duration": 8,
        "file": "01a_establish_split_screen.md",
    },
    "01b": {
        "name": "synchronized_completion",
        "duration": 7,
        "file": "01b_synchronized_completion.md",
    },
    "01c": {
        "name": "brief_satisfaction",
        "duration": 3,
        "file": "01c_brief_satisfaction.md",
    },
    "01d": {
        "name": "zoom_out_reveal",
        "duration": 14,
        "file": "01d_zoom_out_reveal.md",
    },
    "01e": {
        "name": "hold_accumulated_weight",
        "duration": 6,
        "file": "01e_hold_accumulated_weight.md",
    },
}


def extract_prompt(md_content: str, section_name: str = "Concise Version") -> str:
    """Extract a prompt from a markdown file section."""
    # Look for the section header and extract the code block content
    pattern = rf"## {re.escape(section_name)}\s*```\s*(.*?)\s*```"
    match = re.search(pattern, md_content, re.DOTALL)
    if match:
        return match.group(1).strip()
    return ""


def extract_left_prompt(md_content: str) -> str:
    """Extract the left side prompt for compositing."""
    return extract_prompt(md_content, "Left Side Only (If Compositing)")


def extract_right_prompt(md_content: str) -> str:
    """Extract the right side prompt for compositing."""
    return extract_prompt(md_content, "Right Side Only (If Compositing)")


def save_video(client: genai.Client, video, output_path: Path, use_vertexai: bool = False) -> bool:
    """Save a video from the Veo API to a local file."""
    print(f"  Saving video to {output_path}...")

    # Check if video bytes are already available
    if hasattr(video, 'video_bytes') and video.video_bytes:
        try:
            with open(output_path, "wb") as f:
                f.write(video.video_bytes)
            print(f"  Saved from video_bytes: {output_path}")
            return True
        except Exception as e:
            print(f"  Error saving from video_bytes: {e}")

    # For Gemini Developer API, use client.files.download
    if not use_vertexai:
        try:
            client.files.download(file=video)
            video.save(str(output_path))
            print(f"  Saved: {output_path}")
            return True
        except Exception as e:
            print(f"  Error saving video with SDK: {e}")

    # Check if there's a URI (GCS for Vertex AI, or HTTP for Gemini)
    if hasattr(video, 'uri') and video.uri:
        uri = video.uri
        print(f"  Video URI: {uri}")

        # Handle GCS URIs for Vertex AI
        if uri.startswith("gs://"):
            try:
                from google.cloud import storage
                print(f"  Downloading from GCS...")

                # Parse GCS URI: gs://bucket-name/path/to/file
                parts = uri[5:].split("/", 1)
                bucket_name = parts[0]
                blob_path = parts[1] if len(parts) > 1 else ""

                storage_client = storage.Client()
                bucket = storage_client.bucket(bucket_name)
                blob = bucket.blob(blob_path)
                blob.download_to_filename(str(output_path))

                print(f"  Saved from GCS: {output_path}")
                return True
            except ImportError:
                print(f"  google-cloud-storage not installed. Run: pip install google-cloud-storage")
                print(f"  GCS URI for manual download: {uri}")
            except Exception as e:
                print(f"  Error downloading from GCS: {e}")
                print(f"  GCS URI for manual download: {uri}")
        else:
            # Try HTTP download
            try:
                import requests
                print(f"  Downloading from HTTP URI...")
                response = requests.get(uri, stream=True)
                response.raise_for_status()
                with open(output_path, "wb") as f:
                    for chunk in response.iter_content(chunk_size=8192):
                        f.write(chunk)
                print(f"  Saved from HTTP: {output_path}")
                return True
            except Exception as e:
                print(f"  HTTP download failed: {e}")
                print(f"  URI for manual download: {uri}")

    return False


def load_reference_image(image_path: Path):
    """Load a reference image for image-to-video generation."""
    if not image_path.exists():
        print(f"  Warning: Reference image not found: {image_path}")
        return None

    try:
        # Read image bytes and create Image object with mime type
        import mimetypes
        mime_type, _ = mimetypes.guess_type(str(image_path))
        if not mime_type:
            mime_type = "image/png"

        with open(image_path, "rb") as f:
            image_bytes = f.read()

        # Create a types.Image with the bytes
        return types.Image(
            image_bytes=image_bytes,
            mime_type=mime_type
        )
    except Exception as e:
        print(f"  Error loading reference image: {e}")
        import traceback
        traceback.print_exc()
        return None


def generate_video(
    client: genai.Client,
    prompt: str,
    output_path: Path,
    model: str = "veo-3.1-generate-preview",
    poll_interval: int = 20,
    max_wait: int = 600,
    use_vertexai: bool = False,
    reference_image=None,
) -> bool:
    """Generate a video using Veo and save it to the output path."""
    print(f"\nGenerating video: {output_path.name}")
    print(f"  Model: {model}")
    print(f"  Prompt: {prompt[:100]}...")
    if reference_image:
        print(f"  Using reference image for character consistency")

    try:
        # Build the generation arguments
        gen_kwargs = {
            "model": model,
            "prompt": prompt,
            "config": types.GenerateVideosConfig(
                aspect_ratio="16:9",
                number_of_videos=1,
            ),
        }

        # Add reference image if provided
        if reference_image is not None:
            gen_kwargs["image"] = reference_image

        # Start the video generation
        operation = client.models.generate_videos(**gen_kwargs)

        print(f"  Operation started: {operation.name}")

        # Poll until complete
        elapsed = 0
        while not operation.done:
            if elapsed >= max_wait:
                print(f"  Error: Timeout waiting for video generation")
                return False

            print(f"  Waiting... ({elapsed}s elapsed)")
            time.sleep(poll_interval)
            elapsed += poll_interval
            operation = client.operations.get(operation)

        # Check for errors
        if operation.error:
            print(f"  Error: {operation.error}")
            return False

        # Get the generated video from operation.response (not operation.result)
        if not operation.response or not operation.response.generated_videos:
            print(f"  Error: No videos generated")
            return False

        video = operation.response.generated_videos[0].video
        print(f"  Video generated successfully")

        # Save the video
        return save_video(client, video, output_path, use_vertexai=use_vertexai)

    except Exception as e:
        print(f"  Error: {e}")
        import traceback
        traceback.print_exc()
        return False


def main():
    parser = argparse.ArgumentParser(
        description="Generate video segments using Google's Veo API"
    )
    parser.add_argument(
        "--segment",
        type=str,
        help="Generate only this segment (e.g., 01a, 01b)",
        choices=list(SEGMENTS.keys()),
    )
    parser.add_argument(
        "--separate-sides",
        action="store_true",
        help="Generate left and right sides separately for compositing",
    )
    parser.add_argument(
        "--model",
        type=str,
        default="veo-3.1-generate-preview",
        help="Veo model to use (default: veo-3.1-generate-preview)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print prompts without generating videos",
    )
    parser.add_argument(
        "--api-key",
        action="store_true",
        help="Use GOOGLE_API_KEY instead of Vertex AI credentials",
    )
    parser.add_argument(
        "--use-references",
        action="store_true",
        help="Use reference images for character consistency (requires --separate-sides)",
    )
    parser.add_argument(
        "--project",
        type=str,
        default=DEFAULT_PROJECT,
        help=f"Google Cloud project ID (default: {DEFAULT_PROJECT})",
    )
    parser.add_argument(
        "--location",
        type=str,
        default=DEFAULT_LOCATION,
        help=f"Google Cloud location (default: {DEFAULT_LOCATION})",
    )
    args = parser.parse_args()

    # Validate arguments
    if args.use_references and not args.separate_sides:
        print("Warning: --use-references requires --separate-sides, enabling it automatically")
        args.separate_sides = True

    # Initialize the client
    client = None
    if not args.dry_run:
        if args.api_key:
            # Use API key authentication
            api_key = os.environ.get("GOOGLE_API_KEY")
            if not api_key:
                print("Error: GOOGLE_API_KEY environment variable not set")
                sys.exit(1)
            print(f"Using API key authentication")
            client = genai.Client(api_key=api_key)
        else:
            # Use Vertex AI authentication (default)
            creds_path = os.environ.get("GOOGLE_APPLICATION_CREDENTIALS")
            if not creds_path:
                print("Error: GOOGLE_APPLICATION_CREDENTIALS environment variable not set")
                print("Set it to your service account JSON file path, or use --api-key flag")
                sys.exit(1)

            # Get project from credentials file if not specified
            project = args.project
            if project == DEFAULT_PROJECT:
                try:
                    with open(creds_path) as f:
                        creds_data = json.load(f)
                        project = creds_data.get("project_id", DEFAULT_PROJECT)
                except Exception:
                    pass

            print(f"Using Vertex AI authentication")
            print(f"  Project: {project}")
            print(f"  Location: {args.location}")
            print(f"  Credentials: {creds_path}")

            client = genai.Client(
                vertexai=True,
                project=project,
                location=args.location,
            )

    # Set up paths
    script_dir = Path(__file__).parent
    output_dir = script_dir / "outputs"
    output_dir.mkdir(exist_ok=True)

    # Load reference images if requested
    reference_images = {"left": None, "right": None}
    if args.use_references and not args.dry_run:
        print("\nLoading reference images...")
        for side, rel_path in REFERENCE_IMAGES.items():
            img_path = script_dir / rel_path
            if img_path.exists():
                reference_images[side] = load_reference_image(img_path)
                if reference_images[side]:
                    print(f"  Loaded {side} reference: {img_path}")
                else:
                    print(f"  Failed to load {side} reference: {img_path}")
            else:
                print(f"  Reference image not found: {img_path}")
                print(f"  Run 'python generate_references.py' first to create reference images")

        if not any(reference_images.values()):
            print("\nError: No reference images loaded. Run 'python generate_references.py' first.")
            sys.exit(1)

    # Determine which segments to generate
    segments_to_generate = (
        [args.segment] if args.segment else list(SEGMENTS.keys())
    )

    results = {}

    for segment_id in segments_to_generate:
        segment = SEGMENTS[segment_id]
        md_path = script_dir / segment["file"]

        print(f"\n{'='*60}")
        print(f"Segment {segment_id}: {segment['name']}")
        print(f"Duration: {segment['duration']}s")
        print(f"{'='*60}")

        # Read the markdown file
        if not md_path.exists():
            print(f"  Error: {md_path} not found")
            results[segment_id] = False
            continue

        md_content = md_path.read_text()

        if args.separate_sides:
            # Generate left and right sides separately
            left_prompt = extract_left_prompt(md_content)
            right_prompt = extract_right_prompt(md_content)

            if not left_prompt or not right_prompt:
                print(f"  Error: Could not extract left/right prompts")
                results[segment_id] = False
                continue

            print(f"\n  Left side prompt:")
            print(f"    {left_prompt[:100]}...")
            print(f"\n  Right side prompt:")
            print(f"    {right_prompt[:100]}...")

            if args.dry_run:
                results[segment_id] = True
                continue

            # Generate left side
            left_output = output_dir / f"{segment_id}_{segment['name']}_left.mp4"
            left_success = generate_video(
                client, left_prompt, left_output, model=args.model,
                use_vertexai=not args.api_key,
                reference_image=reference_images["left"] if args.use_references else None
            )

            # Generate right side
            right_output = output_dir / f"{segment_id}_{segment['name']}_right.mp4"
            right_success = generate_video(
                client, right_prompt, right_output, model=args.model,
                use_vertexai=not args.api_key,
                reference_image=reference_images["right"] if args.use_references else None
            )

            results[segment_id] = left_success and right_success
        else:
            # Generate combined split-screen video
            prompt = extract_prompt(md_content)

            if not prompt:
                print(f"  Error: Could not extract concise prompt")
                results[segment_id] = False
                continue

            print(f"\n  Prompt:")
            print(f"    {prompt[:150]}...")

            if args.dry_run:
                results[segment_id] = True
                continue

            output_path = output_dir / f"{segment_id}_{segment['name']}.mp4"
            results[segment_id] = generate_video(
                client, prompt, output_path, model=args.model,
                use_vertexai=not args.api_key
            )

    # Print summary
    print(f"\n{'='*60}")
    print("Generation Summary")
    print(f"{'='*60}")

    for segment_id, success in results.items():
        status = "OK" if success else "FAILED"
        print(f"  {segment_id}: {status}")

    total = len(results)
    succeeded = sum(1 for s in results.values() if s)
    print(f"\n  Total: {succeeded}/{total} succeeded")

    if succeeded < total:
        sys.exit(1)


if __name__ == "__main__":
    main()
