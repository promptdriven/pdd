#!/usr/bin/env python3
"""
Example: How to use generate_section_compositions.py

This script demonstrates both:
  1. Running the module as a CLI subprocess (its primary intended use).
  2. Importing and calling its internal functions directly for programmatic use.

Prerequisites:
  - A project directory containing a valid `project.json` file.
  - A Remotion directory structure (e.g., `remotion/src/remotion/`).

Directory layout (relative to project root):
    project_root/
    ├── project.json
    ├── remotion/
    │   └── src/
    │       └── remotion/
    │           └── Root.tsx          (generated/updated by the script)
    └── scripts/
        └── generate_section_compositions.py
"""

import json
import os
import subprocess
import sys
import tempfile
import shutil
from typing import Any, Dict, List

# ---------------------------------------------------------------------------
# Resolve the path to the module dynamically so this example is portable.
# The module lives at: scripts/generate_section_compositions.py
# ---------------------------------------------------------------------------
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
# Adjust this relative path based on where this example file lives vs. the module
MODULE_DIR = os.path.join(SCRIPT_DIR, "..", "scripts")
sys.path.insert(0, MODULE_DIR)

try:
    from generate_section_compositions import (
        to_pascal_case,
        load_project_json,
        get_fps,
        generate_section_component,
        generate_root_tsx,
        emit_progress,
    )
except ImportError:
    # Fallback or warning if the module isn't found in the expected location
    print("Warning: generate_section_compositions.py not found in expected path.")


def create_sample_project(tmpdir: str) -> str:
    """
    Create a minimal project.json for demonstration purposes.

    Parameters
    ----------
    tmpdir : str
        Temporary directory to write the project.json into.

    Returns
    -------
    str
        Path to the temporary project directory.
    """
    project_data = {
        "name": "my-video-project",
        "render": {
            "fps": 30,
            "width": 1920,
            "height": 1080,
        },
        "sections": [
            {
                "id": "intro",
                "durationSeconds": 5,
                "offsetSeconds": 0,
                "compositions": ["title_card", "logo-reveal"],
            },
            {
                "id": "main_content",
                "durationSeconds": 30,
                "offsetSeconds": 5,
                "compositions": ["slide-one", "slide_two"],
            },
            {
                "id": "outro",
                "durationSeconds": 4,
                "offsetSeconds": 35,
                # No sub-compositions — the generated stub will have a placeholder
            },
        ],
    }

    project_path = os.path.join(tmpdir, "project.json")
    with open(project_path, "w", encoding="utf-8") as f:
        json.dump(project_data, f, indent=2)

    # Also create the remotion directory skeleton
    remotion_src = os.path.join(tmpdir, "remotion", "src", "remotion")
    os.makedirs(remotion_src, exist_ok=True)

    return tmpdir


# ===================================================================
# EXAMPLE 1: Using individual helper functions programmatically
# ===================================================================
def example_programmatic_usage() -> None:
    """
    Demonstrates importing and calling the module's public functions
    directly from Python code, without invoking the CLI.
    """
    print("=" * 70)
    print("EXAMPLE 1: Programmatic usage of individual functions")
    print("=" * 70)

    # ---- to_pascal_case ----
    print("\n--- to_pascal_case ---")
    test_ids = ["intro", "section_two", "my-section", "hello_world-test"]
    for sid in test_ids:
        print(f"  '{sid}' -> '{to_pascal_case(sid)}'")

    # ---- get_fps ----
    print("\n--- get_fps ---")
    project_with_fps = {"render": {"fps": 60}}
    project_without_fps = {"render": {}}
    project_empty: Dict[str, Any] = {}
    print(f"  With fps=60 in config: {get_fps(project_with_fps)}")
    print(f"  Without fps in config: {get_fps(project_without_fps)}")
    print(f"  Empty project data:    {get_fps(project_empty)}")

    # ---- generate_section_component ----
    print("\n--- generate_section_component ---")
    section_def = {
        "id": "intro",
        "durationSeconds": 5,
        "offsetSeconds": 0,
        "compositions": ["title_card", "logo-reveal"],
    }
    tsx_output = generate_section_component(section_def, fps=30)
    print("  Generated TSX for 'intro' section:")
    for line in tsx_output.split("\n"):
        print(f"    {line}")

    # Section without compositions (generates a placeholder comment)
    section_no_comps = {
        "id": "outro",
        "durationSeconds": 4,
        "offsetSeconds": 35,
    }
    tsx_no_comps = generate_section_component(section_no_comps, fps=30)
    print("\n  Generated TSX for 'outro' section (no compositions):")
    for line in tsx_no_comps.split("\n"):
        print(f"    {line}")

    # ---- generate_root_tsx ----
    print("\n--- generate_root_tsx ---")
    all_sections = [
        {"id": "intro", "durationSeconds": 5, "offsetSeconds": 0},
        {"id": "main_content", "durationSeconds": 30, "offsetSeconds": 5},
        {"id": "outro", "durationSeconds": 4, "offsetSeconds": 35},
    ]
    root_tsx = generate_root_tsx(all_sections, fps=30, remotion_dir="remotion/")
    print("  Generated Root.tsx:")
    for line in root_tsx.split("\n"):
        print(f"    {line}")


# ===================================================================
# EXAMPLE 2: Running as a CLI subprocess (primary intended usage)
# ===================================================================
def example_cli_subprocess() -> None:
    """
    Demonstrates invoking the script as a subprocess, which is how the
    compositions API route calls it in production.
    """
    print("\n" + "=" * 70)
    print("EXAMPLE 2: Running as a CLI subprocess")
    print("=" * 70)

    tmpdir = tempfile.mkdtemp(prefix="remotion_example_")
    try:
        project_dir = create_sample_project(tmpdir)
        remotion_dir = os.path.join(tmpdir, "remotion")

        script_path = os.path.join(MODULE_DIR, "generate_section_compositions.py")
        if not os.path.isfile(script_path):
            print(f"  [WARN] Script not found at expected path; skipping subprocess demo.")
            return

        # --- First run: generates all files ---
        print("\n  First run (generates all section files):")
        result = subprocess.run(
            [
                sys.executable,
                script_path,
                "--project-dir", project_dir,
                "--remotion-dir", remotion_dir,
            ],
            capture_output=True,
            text=True,
        )

        print(f"  Exit code: {result.returncode}")
        print(f"  Stdout (JSON progress lines):")
        for line in result.stdout.strip().split("\n"):
            if line.strip():
                parsed = json.loads(line)
                print(f"    {json.dumps(parsed, indent=6)}")

        if result.stderr:
            print(f"  Stderr: {result.stderr}")

        # Show generated files
        print("\n  Generated files:")
        for root, dirs, files in os.walk(os.path.join(remotion_dir, "src", "remotion")):
            for fname in files:
                fpath = os.path.join(root, fname)
                rel = os.path.relpath(fpath, tmpdir)
                print(f"    {rel}")

        # --- Second run without --force: should skip all sections ---
        print("\n  Second run (without --force, should skip existing files):")
        result2 = subprocess.run(
            [
                sys.executable,
                script_path,
                "--project-dir", project_dir,
                "--remotion-dir", remotion_dir,
            ],
            capture_output=True,
            text=True,
        )
        print(f"  Exit code: {result2.returncode}")
        for line in result2.stdout.strip().split("\n"):
            if line.strip():
                parsed = json.loads(line)
                print(f"    {json.dumps(parsed, indent=6)}")

        # --- Third run with --force: overwrites all ---
        print("\n  Third run (with --force, overwrites existing files):")
        result3 = subprocess.run(
            [
                sys.executable,
                script_path,
                "--project-dir", project_dir,
                "--remotion-dir", remotion_dir,
                "--force",
            ],
            capture_output=True,
            text=True,
        )
        print(f"  Exit code: {result3.returncode}")
        for line in result3.stdout.strip().split("\n"):
            if line.strip():
                parsed = json.loads(line)
                print(f"    {json.dumps(parsed, indent=6)}")

    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)


# ===================================================================
# EXAMPLE 3: Loading project.json and inspecting data
# ===================================================================
def example_load_project() -> None:
    """
    Demonstrates load_project_json, which reads and parses project.json.
    """
    print("\n" + "=" * 70)
    print("EXAMPLE 3: Loading project.json")
    print("=" * 70)

    tmpdir = tempfile.mkdtemp(prefix="remotion_load_example_")
    try:
        create_sample_project(tmpdir)
        project_data = load_project_json(tmpdir)

        print(f"\n  Project name: {project_data.get('name')}")
        print(f"  FPS: {get_fps(project_data)}")
        print(f"  Number of sections: {len(project_data.get('sections', []))}")
        for section in project_data.get("sections", []):
            sid = section["id"]
            dur = section.get("durationSeconds", 0)
            off = section.get("offsetSeconds", 0)
            comps = section.get("compositions", [])
            print(f"    Section '{sid}': duration={dur}s, offset={off}s, compositions={comps}")
    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)


# ===================================================================
# EXAMPLE 4: emit_progress utility
# ===================================================================
def example_emit_progress() -> None:
    """
    Demonstrates the emit_progress function, which prints structured
    JSON lines to stdout for consumption by the calling API route.
    """
    print("\n" + "=" * 70)
    print("EXAMPLE 4: emit_progress JSON output")
    print("=" * 70)
    print("\n  Calling emit_progress for a completed section:")
    emit_progress(section_id="intro", status="done", path="remotion/src/remotion/intro/index.tsx")

    print("  Calling emit_progress for a skipped section:")
    emit_progress(section_id="intro", status="skipped", reason="already exists")


if __name__ == "__main__":
    example_programmatic_usage()
    example_load_project()
    example_emit_progress()
    example_cli_subprocess()