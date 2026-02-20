#!/usr/bin/env python3
"""Render individual section videos using Remotion CLI.

Runs `npx remotion render` for each section's composition, producing
one MP4 per section in outputs/sections/.

Usage:
    python render_sections.py                       # Render all sections
    python render_sections.py --section cold_open   # Render one section
    python render_sections.py --parallel 3          # Parallel renders
"""

import argparse
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

from utils import (
    REMOTION_DIR, SECTIONS_OUTPUT_DIR,
    load_project_config, get_sections,
    emit_progress, emit_error, emit_done,
)


def render_section(section: dict) -> tuple[str, bool, str]:
    """Render a single section using Remotion CLI."""
    composition_id = section.get("compositionId")
    if not composition_id:
        return (section["id"], False, "No compositionId configured")

    output_dir = SECTIONS_OUTPUT_DIR
    output_dir.mkdir(parents=True, exist_ok=True)
    output_path = output_dir / section["videoFile"]

    cmd = [
        "npx", "remotion", "render",
        composition_id,
        str(output_path),
        "--codec", "h264",
    ]

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            cwd=str(REMOTION_DIR),
            timeout=600,
        )
        if result.returncode != 0:
            return (section["id"], False, f"Render failed: {result.stderr[:200]}")
        return (section["id"], True, f"Rendered {output_path.name}")

    except subprocess.TimeoutExpired:
        return (section["id"], False, "Render timed out (10 min)")
    except Exception as e:
        return (section["id"], False, str(e))


def main():
    parser = argparse.ArgumentParser(description="Render section videos with Remotion")
    parser.add_argument("--section", default="all", help="Section ID or 'all'")
    parser.add_argument("--parallel", type=int, default=1, help="Max parallel renders")
    args = parser.parse_args()

    config = load_project_config()
    max_parallel = args.parallel or config.get("render", {}).get("maxParallelRenders", 3)

    sections = get_sections()
    if args.section != "all":
        sections = [s for s in sections if s["id"] == args.section]
        if not sections:
            emit_error("render", f"Unknown section: {args.section}")
            sys.exit(1)

    emit_progress("render", 5, f"Rendering {len(sections)} section(s)")

    results = {}

    if max_parallel > 1 and len(sections) > 1:
        with ThreadPoolExecutor(max_workers=max_parallel) as executor:
            futures = {executor.submit(render_section, s): s["id"] for s in sections}
            for future in as_completed(futures):
                sid, success, msg = future.result()
                results[sid] = (success, msg)
                pct = int(10 + 80 * len(results) / len(sections))
                emit_progress("render", pct, f"[{sid}] {'OK' if success else 'FAILED'}: {msg}")
    else:
        for i, section in enumerate(sections):
            pct = int(10 + 80 * (i / len(sections)))
            emit_progress("render", pct, f"Rendering {section['label']}...")
            sid, success, msg = render_section(section)
            results[sid] = (success, msg)

    succeeded = sum(1 for s, _ in results.values() if s)
    total = len(results)

    if succeeded == total:
        emit_done("render", f"Rendered {total} section(s)")
    else:
        emit_error("render", f"{succeeded}/{total} sections rendered")
        sys.exit(1)


if __name__ == "__main__":
    main()
