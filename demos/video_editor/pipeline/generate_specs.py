#!/usr/bin/env python3
"""Generate visual specs from the TTS script using Claude.

For each section, produces a spec directory with visual descriptions,
Veo prompts, and Remotion composition outlines.

Usage:
    python generate_specs.py                        # Generate all sections
    python generate_specs.py --section cold_open    # Single section
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path

from utils import (
    NARRATIVE_DIR, SPECS_DIR,
    load_project_config, get_sections,
    emit_progress, emit_error, emit_done,
)

SPEC_PROMPT = """Generate a visual specification for the video section "{label}".

This section's TTS script:
{tts_content}

Create a detailed spec that includes:
1. A README.md with visual descriptions for each narration segment
2. For segments needing Veo-generated video clips, create prompt files in a prompts/ subdirectory
3. Each prompt file should contain a ## Veo Prompt section with a ``` code block containing the prompt

Format the README.md with:
- Section overview
- Visual sequence (numbered list mapping narration segments to visuals)
- Composition types used (Remotion animation, Veo clip, title card, etc.)
- Timing notes from the narration

Output all files as JSON: {{"files": [{{"path": "README.md", "content": "..."}}, ...]}}
"""


def extract_section_tts(tts_content: str, section_label: str) -> str:
    """Extract the TTS script portion for a specific section."""
    lines = tts_content.split("\n")
    in_section = False
    section_lines = []

    for line in lines:
        if line.startswith("## ") and section_label.lower() in line.lower():
            in_section = True
            section_lines.append(line)
            continue
        if in_section and line.startswith("## "):
            break
        if in_section:
            section_lines.append(line)

    return "\n".join(section_lines) if section_lines else tts_content[:2000]


def process_section(section: dict, tts_content: str) -> tuple[str, bool, str]:
    """Generate specs for a single section."""
    section_tts = extract_section_tts(tts_content, section["label"])
    prompt = SPEC_PROMPT.format(label=section["label"], tts_content=section_tts)

    try:
        result = subprocess.run(
            ["claude", "--print", "-p", prompt],
            capture_output=True,
            text=True,
            timeout=180,
        )

        if result.returncode != 0:
            return (section["id"], False, f"Claude failed: {result.stderr[:100]}")

        output = result.stdout.strip()

        # Try to parse as JSON with file list
        try:
            data = json.loads(output)
            files = data.get("files", [])
        except json.JSONDecodeError:
            # Fall back to treating entire output as README
            files = [{"path": "README.md", "content": output}]

        spec_dir = SPECS_DIR / section["specDir"]
        spec_dir.mkdir(parents=True, exist_ok=True)

        for file_info in files:
            file_path = spec_dir / file_info["path"]
            file_path.parent.mkdir(parents=True, exist_ok=True)
            file_path.write_text(file_info["content"])

        return (section["id"], True, f"Generated {len(files)} file(s) in {section['specDir']}/")

    except subprocess.TimeoutExpired:
        return (section["id"], False, "Claude timed out")
    except FileNotFoundError:
        return (section["id"], False, "Claude CLI not found")
    except Exception as e:
        return (section["id"], False, str(e))


def main():
    parser = argparse.ArgumentParser(description="Generate visual specs")
    parser.add_argument("--section", default="all", help="Section ID or 'all'")
    args = parser.parse_args()

    tts_path = NARRATIVE_DIR / "tts_script.md"
    if not tts_path.exists():
        emit_error("specs", f"TTS script not found: {tts_path}. Run tts-script stage first.")
        sys.exit(1)

    tts_content = tts_path.read_text()

    sections = get_sections()
    if args.section != "all":
        sections = [s for s in sections if s["id"] == args.section]
        if not sections:
            emit_error("specs", f"Unknown section: {args.section}")
            sys.exit(1)

    emit_progress("specs", 5, f"Generating specs for {len(sections)} section(s)")

    results = {}
    for i, section in enumerate(sections):
        pct = int(10 + 80 * (i / max(1, len(sections))))
        emit_progress("specs", pct, f"Processing {section['label']}...")
        sid, success, msg = process_section(section, tts_content)
        results[sid] = (success, msg)

    succeeded = sum(1 for s, _ in results.values() if s)
    total = len(results)

    if succeeded == total:
        emit_done("specs", f"Generated specs for {total} section(s)")
    else:
        emit_error("specs", f"{succeeded}/{total} sections generated")
        sys.exit(1)


if __name__ == "__main__":
    main()
