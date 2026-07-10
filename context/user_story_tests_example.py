from __future__ import annotations

import os
import sys
from pathlib import Path
from pdd.user_story_tests import (
    story_id,
    discover_story_files,
    parse_story_dev_unit_metadata,
    get_all_dev_units_for_story,
    story_is_cross_unit,
    get_cross_unit_stories_for_prompt,
)

def main() -> None: 
    # 1. Setup the output directory for mock artifacts as requested
    output_dir = Path("./output")
    output_dir.mkdir(parents=True, exist_ok=True)

    # 2. Create mock user story files to demonstrate discovery and parsing
    # We will create a cross-unit story (references multiple dev units)
    cross_unit_story_path = output_dir / "story__multi_payment_flow.md"
    cross_unit_story_content = """<!-- pdd-story-prompts: auth_service.prompt, stripe_billing.prompt -->
<!-- pdd-story-dev-units: auth_service.prompt, stripe_billing.prompt -->

# User Story: Multi-Payment Checkout Flow

## Story
As a premium subscriber, I want to authenticate and pay using Stripe so that my subscription is immediately activated.
"""
    cross_unit_story_path.write_text(cross_unit_story_content, encoding="utf-8")

    # Create a single-unit story
    single_unit_story_path = output_dir / "story__simple_login.md"
    single_unit_story_content = """<!-- pdd-story-prompts: auth_service.prompt -->

# User Story: Simple Login

## Story
As a registered user, I want to sign in with my password so that I can access my profile.
"""
    single_unit_story_path.write_text(single_unit_story_content, encoding="utf-8")

    print("--- [1] Extracting Story IDs (Slugs) ---")
    # The story_id helper maps a 'story__<slug>.md' file path to its canonical '<slug>' identity
    slug_1 = story_id(cross_unit_story_path)
    slug_2 = story_id(single_unit_story_path)
    print(f"Path: {cross_unit_story_path.name} -> Story ID: {slug_1}")
    print(f"Path: {single_unit_story_path.name} -> Story ID: {slug_2}\n")

    print("--- [2] Parsing Dev Unit & Story Metadata ---")
    # Read and parse metadata directly from the story texts
    for path in [cross_unit_story_path, single_unit_story_path]:
        text = path.read_text(encoding="utf-8")
        
        # Extract explicitly declared dev-units (pdd-story-dev-units)
        dev_units = parse_story_dev_unit_metadata(text)
        
        # Get union of all dev units/prompts associated with the story (order-preserved, deduplicated)
        all_units = get_all_dev_units_for_story(text)
        
        # Check if the story is cross-unit (spans 2 or more dev units/prompts)
        is_cross = story_is_cross_unit(text)
        
        print(f"Story: {path.name}")
        print(f"  - Extracted Dev Units: {dev_units}")
        print(f"  - All Associated Units: {all_units}")
        print(f"  - Is Cross-Unit Story? {is_cross}\n")

    print("--- [3] Discovering Story Files ---")
    # Discover all matching story__*.md files in our output directory
    discovered_stories = discover_story_files(stories_dir=str(output_dir))
    print(f"Found {len(discovered_stories)} story file(s) in {output_dir}:")
    for story in discovered_stories:
        print(f"  - {story.relative_to(output_dir.parent)}")
    print("")

    print("--- [4] Performing Forward Lookup (Prompt -> Cross-Unit Stories) ---")
    # Find all cross-unit stories in our directory associated with 'stripe_billing.prompt'
    target_prompt = "stripe_billing.prompt"
    matching_cross_stories = get_cross_unit_stories_for_prompt(
        prompt_name=target_prompt, 
        stories_dir=output_dir
    )
    
    print(f"Cross-unit stories referencing '{target_prompt}':")
    for match in matching_cross_stories:
        print(f"  - Story Name: {match['story']}")
        print(f"    Story ID:   {match['story_id']}")
        print(f"    Dev Units:  {match['dev_units']}")
        print(f"    File Path:  {match['path']}")

if __name__ == "__main__":
    main()