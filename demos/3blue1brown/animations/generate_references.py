#!/usr/bin/env python3
"""
Generate reference images for character consistency in video segments.

Usage:
    python generate_references.py

This generates reference images for:
- Left side: Software developer at desk
- Right side: 1950s grandmother darning socks
"""

import json
import os
import sys
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

# Character reference prompts - detailed and consistent
DEVELOPER_PROMPT = """
Portrait photo of a 32-year-old male software developer at a minimalist desk.
- Short dark brown hair, neatly trimmed
- Light stubble beard
- Rectangular black-framed glasses
- Wearing a dark navy blue hoodie
- Pale complexion with slight under-eye circles
- Focused, intelligent expression
- Single computer monitor with dark code editor visible casting blue glow
- Dark room with modern tech aesthetic
- Cool blue ambient lighting from monitor

Medium shot, upper body and desk visible. Photorealistic, cinematic lighting,
shallow depth of field, 4K quality, professional photography style.
"""

GRANDMOTHER_PROMPT = """
Portrait photo of a 75-year-old grandmother in 1950s domestic setting.
- Silver-gray hair in a neat bun
- Warm, kind face with gentle wrinkles
- Wire-rimmed round spectacles
- Wearing a cream-colored knit cardigan over floral print dress
- Weathered but gentle hands
- Sitting in worn wooden chair
- Small side table with oil lamp casting warm amber glow
- Holding wooden darning egg with gray wool sock
- Cozy domestic interior with period-accurate 1950s details
- Warm amber/golden lighting

Medium shot, upper body visible. Photorealistic, cinematic lighting,
shallow depth of field, 4K quality, nostalgic documentary style.
"""


def generate_image(client: genai.Client, prompt: str, output_path: Path) -> bool:
    """Generate an image using Imagen and save it."""
    print(f"\nGenerating image: {output_path.name}")
    print(f"  Prompt: {prompt[:80]}...")

    try:
        # Use Imagen for image generation
        response = client.models.generate_images(
            model="imagen-3.0-generate-002",
            prompt=prompt,
            config=types.GenerateImagesConfig(
                number_of_images=1,
                aspect_ratio="16:9",
                person_generation="allow_adult",
            ),
        )

        if not response.generated_images:
            print("  Error: No images generated")
            return False

        image = response.generated_images[0].image

        # Save the image
        if hasattr(image, 'image_bytes') and image.image_bytes:
            with open(output_path, "wb") as f:
                f.write(image.image_bytes)
            print(f"  Saved: {output_path}")
            return True
        else:
            # Try using save method
            image.save(str(output_path))
            print(f"  Saved: {output_path}")
            return True

    except Exception as e:
        print(f"  Error: {e}")
        import traceback
        traceback.print_exc()
        return False


def main():
    # Check for credentials
    creds_path = os.environ.get("GOOGLE_APPLICATION_CREDENTIALS")
    if not creds_path:
        print("Error: GOOGLE_APPLICATION_CREDENTIALS environment variable not set")
        sys.exit(1)

    # Get project from credentials
    project = DEFAULT_PROJECT
    try:
        with open(creds_path) as f:
            creds_data = json.load(f)
            project = creds_data.get("project_id", DEFAULT_PROJECT)
    except Exception:
        pass

    print(f"Using Vertex AI authentication")
    print(f"  Project: {project}")
    print(f"  Location: {DEFAULT_LOCATION}")

    client = genai.Client(
        vertexai=True,
        project=project,
        location=DEFAULT_LOCATION,
    )

    # Set up output directory
    script_dir = Path(__file__).parent
    refs_dir = script_dir / "references"
    refs_dir.mkdir(exist_ok=True)

    # Generate reference images
    results = {}

    print("\n" + "=" * 60)
    print("Generating Developer Reference Image")
    print("=" * 60)
    results["developer"] = generate_image(
        client,
        DEVELOPER_PROMPT,
        refs_dir / "developer_reference.png"
    )

    print("\n" + "=" * 60)
    print("Generating Grandmother Reference Image")
    print("=" * 60)
    results["grandmother"] = generate_image(
        client,
        GRANDMOTHER_PROMPT,
        refs_dir / "grandmother_reference.png"
    )

    # Summary
    print("\n" + "=" * 60)
    print("Generation Summary")
    print("=" * 60)
    for name, success in results.items():
        status = "OK" if success else "FAILED"
        print(f"  {name}: {status}")

    if all(results.values()):
        print(f"\nReference images saved to: {refs_dir}/")
        print("\nNext steps:")
        print("  1. Review the generated images")
        print("  2. Run: python generate_segments.py --use-references --separate-sides")
    else:
        sys.exit(1)


if __name__ == "__main__":
    main()
