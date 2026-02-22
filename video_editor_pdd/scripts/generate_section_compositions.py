#!/usr/bin/env python3
"""
generate_section_compositions.py

Scaffolds Remotion section wrapper TSX components from the project.json section registry.
Invoked by the compositions API route as a subprocess.

Usage:
    python scripts/generate_section_compositions.py --project-dir . --remotion-dir remotion/ [--force]
"""

import argparse
import json
import os
import re
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional


def to_pascal_case(section_id: str) -> str:
    """Convert a section ID to PascalCase.

    Examples:
        intro -> Intro
        section_two -> SectionTwo
        my-section -> MySection
        hello_world-test -> HelloWorldTest
    """
    parts = re.split(r'[_\-]', section_id)
    return ''.join(part.capitalize() for part in parts if part)


def load_project_json(project_dir: str) -> Dict[str, Any]:
    """Load and parse project.json from the given directory."""
    project_path = os.path.join(project_dir, 'project.json')
    if not os.path.isfile(project_path):
        print(json.dumps({
            "error": f"project.json not found at {project_path}"
        }), flush=True)
        sys.exit(1)

    with open(project_path, 'r', encoding='utf-8') as f:
        return json.load(f)


def get_fps(project_data: Dict[str, Any]) -> int:
    """Extract FPS from project.json render config, defaulting to 30."""
    render_config = project_data.get('render', {})
    return int(render_config.get('fps', 30))


def generate_section_component(
    section: Dict[str, Any],
    fps: int,
) -> str:
    """Generate the TSX source code for a section wrapper component."""
    section_id = section['id']
    pascal_name = to_pascal_case(section_id)
    component_name = f'{pascal_name}Section'
    duration_seconds = section.get('durationSeconds', 0)
    offset_seconds = section.get('offsetSeconds', 0)
    compositions: List[Dict[str, Any]] = section.get('compositions', [])

    lines: List[str] = []

    # Imports
    lines.append('import React from "react";')
    lines.append('import { Sequence } from "remotion";')
    lines.append('')

    # Import sub-compositions if present
    if compositions:
        for comp in compositions:
            comp_id = comp if isinstance(comp, str) else comp.get('id', '')
            if comp_id:
                comp_pascal = to_pascal_case(comp_id)
                # Sub-compositions are assumed to be sibling directories or relative imports
                lines.append(f'import {{ {comp_pascal} }} from "../{comp_id}";')
        lines.append('')

    # Calculate frame values
    from_frame = f'{offset_seconds} * {fps}'
    duration_frames = f'{duration_seconds} * {fps}'

    # Component definition
    lines.append(f'export const {component_name}: React.FC = () => {{')
    lines.append(f'  const fps = {fps};')
    lines.append(f'  const offsetSeconds = {offset_seconds};')
    lines.append(f'  const durationSeconds = {duration_seconds};')
    lines.append('')
    lines.append('  return (')
    lines.append(f'    <Sequence from={{offsetSeconds * fps}} durationInFrames={{durationSeconds * fps}}>')

    if compositions:
        for comp in compositions:
            comp_id = comp if isinstance(comp, str) else comp.get('id', '')
            if comp_id:
                comp_pascal = to_pascal_case(comp_id)
                lines.append(f'      <{comp_pascal} />')
    else:
        lines.append('      {/* Sub-compositions will be added here */}')

    lines.append('    </Sequence>')
    lines.append('  );')
    lines.append('};')
    lines.append('')
    lines.append(f'export default {component_name};')
    lines.append('')

    return '\n'.join(lines)


def generate_root_tsx(
    sections: List[Dict[str, Any]],
    fps: int,
    remotion_dir: str,
) -> str:
    """Generate the Root.tsx content that registers all section compositions."""
    lines: List[str] = []

    lines.append('import React from "react";')
    lines.append('import { Composition } from "remotion";')
    lines.append('')

    # Import all section components
    for section in sections:
        section_id = section['id']
        pascal_name = to_pascal_case(section_id)
        component_name = f'{pascal_name}Section'
        lines.append(f'import {{ {component_name} }} from "./{section_id}";')

    lines.append('')
    lines.append('export const RemotionRoot: React.FC = () => {')
    lines.append('  return (')
    lines.append('    <>')

    for section in sections:
        section_id = section['id']
        pascal_name = to_pascal_case(section_id)
        component_name = f'{pascal_name}Section'
        duration_seconds = section.get('durationSeconds', 0)
        duration_frames = duration_seconds * fps
        # Use a reasonable default width/height
        width = section.get('width', 1920)
        height = section.get('height', 1080)

        lines.append(f'      <Composition')
        lines.append(f'        id="{section_id}"')
        lines.append(f'        component={{{component_name}}}')
        lines.append(f'        durationInFrames={{{duration_frames}}}')
        lines.append(f'        fps={{{fps}}}')
        lines.append(f'        width={{{width}}}')
        lines.append(f'        height={{{height}}}')
        lines.append(f'      />')

    lines.append('    </>')
    lines.append('  );')
    lines.append('};')
    lines.append('')

    return '\n'.join(lines)


def update_root_tsx(
    sections: List[Dict[str, Any]],
    fps: int,
    remotion_dir: str,
) -> None:
    """Update or create Root.tsx to register all section compositions."""
    root_path = os.path.join(remotion_dir, 'src', 'remotion', 'Root.tsx')
    root_dir = os.path.dirname(root_path)
    os.makedirs(root_dir, exist_ok=True)

    if os.path.isfile(root_path):
        with open(root_path, 'r', encoding='utf-8') as f:
            existing_content = f.read()

        # Strategy: rebuild the file with updated imports and compositions
        # We'll try to preserve any non-section content, but if the file
        # was generated by us, we replace it entirely.

        # Check if this is a file we generated (has our marker pattern)
        # For robustness, we use regex to find and replace composition blocks

        new_content = _merge_root_tsx(existing_content, sections, fps)
    else:
        new_content = generate_root_tsx(sections, fps, remotion_dir)

    with open(root_path, 'w', encoding='utf-8') as f:
        f.write(new_content)


def _merge_root_tsx(
    existing_content: str,
    sections: List[Dict[str, Any]],
    fps: int,
) -> str:
    """Merge section compositions into an existing Root.tsx file.

    Uses regex to find existing <Composition> blocks and replace/append
    section entries. Also ensures imports are present.
    """
    content = existing_content

    # Build the set of section imports and compositions we need
    import_lines: List[str] = []
    composition_lines: List[str] = []

    for section in sections:
        section_id = section['id']
        pascal_name = to_pascal_case(section_id)
        component_name = f'{pascal_name}Section'
        duration_seconds = section.get('durationSeconds', 0)
        duration_frames = duration_seconds * fps
        width = section.get('width', 1920)
        height = section.get('height', 1080)

        import_line = f'import {{ {component_name} }} from "./{section_id}";'
        import_lines.append(import_line)

        comp_block = (
            f'      <Composition\n'
            f'        id="{section_id}"\n'
            f'        component={{{component_name}}}\n'
            f'        durationInFrames={{{duration_frames}}}\n'
            f'        fps={{{fps}}}\n'
            f'        width={{{width}}}\n'
            f'        height={{{height}}}\n'
            f'      />'
        )
        composition_lines.append(comp_block)

    # Remove existing section imports (lines importing from ./sectionId)
    section_ids = {s['id'] for s in sections}
    existing_lines = content.split('\n')
    filtered_lines: List[str] = []
    for line in existing_lines:
        # Check if this line is an import for one of our sections
        import_match = re.match(r'import\s+\{.*\}\s+from\s+["\']\.\/(\w[\w\-]*)["\']\s*;', line)
        if import_match and import_match.group(1) in section_ids:
            continue  # Skip, we'll re-add it
        filtered_lines.append(line)

    content = '\n'.join(filtered_lines)

    # Add our imports after the last existing import line
    last_import_idx = -1
    lines = content.split('\n')
    for i, line in enumerate(lines):
        if line.strip().startswith('import '):
            last_import_idx = i

    if last_import_idx >= 0:
        for imp in reversed(import_lines):
            if imp not in content:
                lines.insert(last_import_idx + 1, imp)
    else:
        # No imports found, add at the top
        for imp in reversed(import_lines):
            lines.insert(0, imp)

    content = '\n'.join(lines)

    # Remove existing <Composition> blocks for our section IDs
    for section in sections:
        section_id = section['id']
        # Match <Composition ... id="section_id" ... /> (possibly multiline)
        pattern = re.compile(
            r'\s*<Composition\s[^>]*id=["\']' + re.escape(section_id) + r'["\'][^>]*/>\s*',
            re.DOTALL
        )
        # Also handle multi-line Composition blocks
        pattern_multiline = re.compile(
            r'\s*<Composition\s*\n(?:\s+\S+.*\n)*?\s+id=["\']' + re.escape(section_id) + r'["\'].*?\n(?:\s+\S+.*\n)*?\s*/>\s*',
            re.DOTALL
        )
        content = pattern_multiline.sub('\n', content)
        content = pattern.sub('\n', content)

    # Find the fragment or return block to insert our compositions
    # Look for </> or a closing fragment tag
    close_fragment_match = re.search(r'(\s*</>\s*)', content)
    if close_fragment_match:
        insert_pos = close_fragment_match.start()
        compositions_block = '\n'.join(composition_lines) + '\n'
        content = content[:insert_pos] + compositions_block + content[insert_pos:]
    else:
        # If no fragment found, look for the return statement and wrap
        return_match = re.search(r'return\s*\(\s*\n', content)
        if return_match:
            insert_pos = return_match.end()
            compositions_block = '    <>\n' + '\n'.join(composition_lines) + '\n    </>\n'
            # Find the closing ); and replace
            content = content[:insert_pos] + compositions_block + '  );\n'
        else:
            # Fallback: regenerate entirely
            content = generate_root_tsx(sections, fps, '')

    return content


def emit_progress(section_id: str, status: str, path: Optional[str] = None, reason: Optional[str] = None) -> None:
    """Print a JSON progress line to stdout."""
    msg: Dict[str, str] = {
        "sectionId": section_id,
        "status": status,
    }
    if path is not None:
        msg["path"] = path
    if reason is not None:
        msg["reason"] = reason

    print(json.dumps(msg), flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(
        description='Generate Remotion section wrapper TSX components from project.json'
    )
    parser.add_argument(
        '--project-dir',
        default='.',
        help='Path to the project directory containing project.json (default: .)'
    )
    parser.add_argument(
        '--remotion-dir',
        default='remotion/',
        help='Path to the Remotion directory (default: remotion/)'
    )
    parser.add_argument(
        '--force',
        action='store_true',
        default=False,
        help='Overwrite existing section files if set'
    )

    args = parser.parse_args()

    project_dir: str = args.project_dir
    remotion_dir: str = args.remotion_dir
    force: bool = args.force

    # Load project.json
    project_data = load_project_json(project_dir)

    # Extract sections
    sections: List[Dict[str, Any]] = project_data.get('sections', [])
    if not sections:
        print(json.dumps({"warning": "No sections found in project.json"}), flush=True)
        sys.exit(0)

    # Get FPS
    fps = get_fps(project_data)

    # Generate section components
    for section in sections:
        section_id = section.get('id')
        if not section_id:
            print(json.dumps({
                "warning": "Section missing 'id' field, skipping",
                "section": section
            }), flush=True)
            continue

        # Determine output path
        section_dir = os.path.join(remotion_dir, 'src', 'remotion', section_id)
        output_path = os.path.join(section_dir, 'index.tsx')
        relative_path = output_path  # Keep as relative for progress output

        # Check if file already exists
        if os.path.isfile(output_path) and not force:
            emit_progress(
                section_id=section_id,
                status='skipped',
                path=relative_path,
                reason='already exists'
            )
            continue

        # Create directory
        os.makedirs(section_dir, exist_ok=True)

        # Generate component source
        tsx_content = generate_section_component(section, fps)

        # Write file
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(tsx_content)

        emit_progress(
            section_id=section_id,
            status='done',
            path=relative_path
        )

    # Update Root.tsx
    update_root_tsx(sections, fps, remotion_dir)

    sys.exit(0)


if __name__ == '__main__':
    main()