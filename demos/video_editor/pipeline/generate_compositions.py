#!/usr/bin/env python3
"""Generate Remotion section compositions synced to audio timestamps.

Creates constants.ts, component TSX, and index.ts for each section wrapper.
These compositions play section narration and sequence through sub-compositions
keyed to Whisper timestamps.

Usage:
    python generate_compositions.py                     # Generate all sections
    python generate_compositions.py --section cold_open # Single section
"""

import argparse
import json
import math
import sys
from pathlib import Path

from utils import (
    PROJECT_ROOT, REMOTION_DIR, TTS_OUTPUT_DIR,
    load_project_config, get_sections,
    emit_progress, emit_error, emit_done,
)

FPS = 30
REMOTION_SRC = REMOTION_DIR / "src" / "remotion"


def s2f(seconds: float) -> int:
    """Convert seconds to frame count at FPS."""
    return round(seconds * FPS)


def load_timestamps(section: dict) -> dict | None:
    """Load word_timestamps.json for a section."""
    tts_dir = section.get("specDir", "")
    path = TTS_OUTPUT_DIR / tts_dir / "word_timestamps.json"
    if not path.exists():
        return None
    with open(path) as f:
        return json.load(f)


def generate_constants(section: dict, ts_data: dict) -> str:
    """Generate constants.ts content for a section."""
    segments = ts_data["segments"]
    duration = ts_data["duration"]
    prefix = section["id"].upper().replace("-", "_")
    comp_name = section["compositionId"]
    duration_seconds = math.ceil(duration) + 2

    narration_lines = []
    for i, seg in enumerate(segments):
        text = seg["text"][:55]
        suffix = '..."' if len(seg["text"]) > 55 else '"'
        narration_lines.append(f'//  {seg["start"]:6.1f}s [{i:2d}] "{text}{suffix}')

    beats_lines = []
    for i, seg in enumerate(segments):
        beats_lines.append(f"  SEGMENT_{i:02d}_START: s2f({seg['start']}),")
        beats_lines.append(f"  SEGMENT_{i:02d}_END: s2f({seg['end']}),")

    return f'''import {{ z }} from "zod";

// Audio-synced timing for {section["label"]}
// Audio: {section["id"]}_narration.wav ({duration:.1f}s)
// Generated from word_timestamps.json
//
// Narration segments:
{chr(10).join(narration_lines)}

export const {prefix}_FPS = {FPS};
export const {prefix}_DURATION_SECONDS = {duration_seconds};
export const {prefix}_DURATION_FRAMES = {prefix}_FPS * {prefix}_DURATION_SECONDS;
export const {prefix}_WIDTH = 1920;
export const {prefix}_HEIGHT = 1080;

const s2f = (seconds: number) => Math.round(seconds * {prefix}_FPS);

export const BEATS = {{
{chr(10).join(beats_lines)}
}};

export const {comp_name}Props = z.object({{
  showTitle: z.boolean().default(true),
}});

export const default{comp_name}Props: z.infer<typeof {comp_name}Props> = {{
  showTitle: true,
}};

export type {comp_name}PropsType = z.infer<typeof {comp_name}Props>;
'''


def generate_component(section: dict) -> str:
    """Generate the main component TSX for a section."""
    comp_name = section["compositionId"]

    return f'''import React from "react";
import {{
  AbsoluteFill,
  Audio,
  staticFile,
  useCurrentFrame,
}} from "remotion";
import {{ BEATS, {comp_name}PropsType }} from "./constants";

export const {comp_name}: React.FC<{comp_name}PropsType> = () => {{
  const frame = useCurrentFrame();

  return (
    <AbsoluteFill style={{{{ backgroundColor: "#0a0a1a" }}}}>
      {{/* Narration audio */}}
      <Audio src={{staticFile("{section['id']}_narration.wav")}} />

      {{/* Visual compositions will be added by generate_section_compositions.py */}}
      <AbsoluteFill style={{{{
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        color: "#ffffff",
        fontFamily: "'SF Pro Display', sans-serif",
        fontSize: 24,
      }}}}>
        {section["label"]}
      </AbsoluteFill>
    </AbsoluteFill>
  );
}};
'''


def generate_index(section: dict) -> str:
    """Generate index.ts for a section composition."""
    comp_name = section["compositionId"]
    prefix = section["id"].upper().replace("-", "_")

    return f'''export {{ {comp_name} }} from "./{comp_name}";
export {{
  {prefix}_FPS,
  {prefix}_DURATION_FRAMES,
  {prefix}_WIDTH,
  {prefix}_HEIGHT,
  {comp_name}Props,
  default{comp_name}Props,
}} from "./constants";
'''


def process_section(section: dict) -> tuple[str, bool, str]:
    """Generate all composition files for a section."""
    ts_data = load_timestamps(section)
    if not ts_data:
        return (section["id"], False, f"No word_timestamps.json found for {section['specDir']}")

    remotion_dir = section.get("remotionDir", "")
    if not remotion_dir:
        return (section["id"], False, "No remotionDir configured")

    folder = REMOTION_SRC / remotion_dir
    folder.mkdir(parents=True, exist_ok=True)

    # Generate constants.ts
    constants = generate_constants(section, ts_data)
    (folder / "constants.ts").write_text(constants)

    # Generate component TSX
    component = generate_component(section)
    (folder / f"{section['compositionId']}.tsx").write_text(component)

    # Generate index.ts
    index = generate_index(section)
    (folder / "index.ts").write_text(index)

    return (section["id"], True, f"Generated 3 files in {remotion_dir}/")


def main():
    parser = argparse.ArgumentParser(description="Generate Remotion section compositions")
    parser.add_argument("--section", default="all", help="Section ID or 'all'")
    args = parser.parse_args()

    sections = get_sections()
    if args.section != "all":
        sections = [s for s in sections if s["id"] == args.section]
        if not sections:
            emit_error("compositions", f"Unknown section: {args.section}")
            sys.exit(1)

    results = {}
    for i, section in enumerate(sections):
        pct = int(10 + 80 * (i / max(1, len(sections))))
        emit_progress("compositions", pct, f"Processing {section['label']}...")

        section_id, success, msg = process_section(section)
        results[section_id] = (success, msg)
        emit_progress("compositions", pct, f"[{section_id}] {'OK' if success else 'FAILED'}: {msg}")

    succeeded = sum(1 for s, _ in results.values() if s)
    total = len(results)

    if succeeded == total:
        emit_done("compositions", f"Generated compositions for {total} section(s)")
    else:
        emit_error("compositions", f"{succeeded}/{total} sections generated")
        sys.exit(1)


if __name__ == "__main__":
    main()
