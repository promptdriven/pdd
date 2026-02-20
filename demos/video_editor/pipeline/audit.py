#!/usr/bin/env python3
"""Audit pipeline: run Claude agents to review rendered video sections.

Spawns parallel Claude Code agents that review each section's output
against its spec, checking for visual accuracy, timing sync, and quality.

Usage:
    python audit.py                         # Audit all sections
    python audit.py --section cold_open     # Audit one section
"""

import argparse
import json
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

from utils import (
    SECTIONS_OUTPUT_DIR, SPECS_DIR,
    load_project_config, get_sections,
    emit_progress, emit_error, emit_done,
)


def audit_section(section: dict) -> tuple[str, bool, str]:
    """Run a Claude Code audit on a single section."""
    video_path = SECTIONS_OUTPUT_DIR / section["videoFile"]
    spec_dir = SPECS_DIR / section["specDir"]

    if not video_path.exists():
        return (section["id"], False, f"Video not found: {section['videoFile']}")

    # Build audit prompt
    spec_readme = spec_dir / "README.md"
    spec_context = ""
    if spec_readme.exists():
        spec_context = spec_readme.read_text()[:3000]

    prompt = f"""Review the rendered video section "{section['label']}" for quality.

Video file: {video_path}
Spec directory: {spec_dir}

Spec context:
{spec_context}

Check for:
1. Visual accuracy against the spec
2. Audio-visual sync (narration matches visuals)
3. Transition quality between visual compositions
4. Overall production quality

Output a JSON object with:
- "score": 1-10 quality score
- "issues": list of issue descriptions
- "suggestions": list of improvement suggestions
"""

    try:
        result = subprocess.run(
            ["claude", "--print", "-p", prompt],
            capture_output=True,
            text=True,
            timeout=120,
        )

        if result.returncode != 0:
            return (section["id"], False, f"Claude audit failed: {result.stderr[:100]}")

        output = result.stdout.strip()
        # Try to parse as JSON
        try:
            audit_result = json.loads(output)
            score = audit_result.get("score", 0)
            issues = len(audit_result.get("issues", []))
            return (section["id"], True, f"Score: {score}/10, {issues} issue(s)")
        except json.JSONDecodeError:
            return (section["id"], True, f"Audit complete (non-JSON response)")

    except subprocess.TimeoutExpired:
        return (section["id"], False, "Audit timed out (2 min)")
    except FileNotFoundError:
        return (section["id"], False, "Claude CLI not found")
    except Exception as e:
        return (section["id"], False, str(e))


def main():
    parser = argparse.ArgumentParser(description="Audit rendered video sections")
    parser.add_argument("--section", default="all", help="Section ID or 'all'")
    parser.add_argument("--parallel", type=int, default=3, help="Max parallel audits")
    args = parser.parse_args()

    sections = get_sections()
    if args.section != "all":
        sections = [s for s in sections if s["id"] == args.section]
        if not sections:
            emit_error("audit", f"Unknown section: {args.section}")
            sys.exit(1)

    emit_progress("audit", 5, f"Auditing {len(sections)} section(s)")

    results = {}

    if args.parallel > 1 and len(sections) > 1:
        with ThreadPoolExecutor(max_workers=args.parallel) as executor:
            futures = {executor.submit(audit_section, s): s["id"] for s in sections}
            for future in as_completed(futures):
                sid, success, msg = future.result()
                results[sid] = (success, msg)
                pct = int(10 + 80 * len(results) / len(sections))
                emit_progress("audit", pct, f"[{sid}] {'OK' if success else 'FAILED'}: {msg}")
    else:
        for i, section in enumerate(sections):
            pct = int(10 + 80 * (i / len(sections)))
            emit_progress("audit", pct, f"Auditing {section['label']}...")
            sid, success, msg = audit_section(section)
            results[sid] = (success, msg)

    succeeded = sum(1 for s, _ in results.values() if s)
    total = len(results)

    if succeeded == total:
        emit_done("audit", f"Audited {total} section(s)")
    else:
        emit_error("audit", f"{succeeded}/{total} sections audited")
        sys.exit(1)


if __name__ == "__main__":
    main()
