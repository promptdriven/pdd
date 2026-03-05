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
import math
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
    remotion_public: str = '',
    remotion_src: str = '',
) -> str:
    """Generate the TSX source code for a section wrapper component.

    When a Claude-generated flat section file ({ComponentName}.tsx) exists in
    remotion_src, the wrapper delegates to it (imports as Base) and only adds
    sub-compositions on top.  Otherwise renders its own Audio/Video.
    """
    section_id = section['id']
    pascal_name = to_pascal_case(section_id)
    component_name = f'{pascal_name}Section'
    duration_seconds = section.get('durationSeconds', 0)
    offset_seconds = section.get('offsetSeconds', 0)
    compositions: List[Dict[str, Any]] = section.get('compositions', [])

    # Check for flat section file to delegate to
    has_flat_file = False
    if remotion_src:
        flat_file_path = os.path.join(remotion_src, f'{component_name}.tsx')
        has_flat_file = os.path.isfile(flat_file_path)

    # Detect available assets in remotion/public/ (only when NOT delegating)
    has_narration = False
    has_veo_clip = False
    if not has_flat_file and remotion_public:
        narration_path = os.path.join(remotion_public, section_id, 'narration.wav')
        has_narration = os.path.isfile(narration_path)
        veo_clip_path = os.path.join(remotion_public, 'veo', f'{section_id}.mp4')
        has_veo_clip = os.path.isfile(veo_clip_path)

    lines: List[str] = []

    # Imports
    remotion_imports = ['Sequence']
    if not has_flat_file:
        if has_narration:
            remotion_imports.append('Audio')
        if has_veo_clip:
            remotion_imports.append('OffthreadVideo')
        if has_narration or has_veo_clip:
            remotion_imports.append('staticFile')

    lines.append('import React from "react";')
    lines.append(f'import {{ {", ".join(remotion_imports)} }} from "remotion";')
    lines.append('')

    # Import flat file as Base when delegating
    if has_flat_file:
        lines.append(f'import {{ {component_name} as {component_name}Base }} from "../{component_name}";')

    # Import sub-compositions if present
    if compositions:
        for comp in compositions:
            comp_id = comp if isinstance(comp, str) else comp.get('id', '')
            if comp_id:
                comp_pascal = to_pascal_case(comp_id)
                lines.append(f'import {{ {comp_pascal} }} from "../{comp_id}";')

    if has_flat_file or compositions:
        lines.append('')

    # Component definition
    lines.append(f'export const {component_name}: React.FC = () => {{')
    lines.append(f'  const fps = {fps};')
    lines.append(f'  const offsetSeconds = {offset_seconds};')
    lines.append(f'  const durationSeconds = {duration_seconds};')
    lines.append('')
    lines.append('  return (')
    lines.append(f'    <Sequence from={{0}} durationInFrames={{Math.ceil(durationSeconds * fps)}}>')

    if has_flat_file:
        # Delegate to flat file for base content (video, audio, subtitles)
        lines.append(f'      <{component_name}Base />')
    else:
        # Render Audio/Video directly
        if has_narration:
            lines.append(f'      <Audio src={{staticFile("{section_id}/narration.wav")}} />')
        if has_veo_clip:
            lines.append(f'      <OffthreadVideo src={{staticFile("veo/{section_id}.mp4")}} style={{{{ width: "100%", height: "100%" }}}} />')

    # Sub-compositions rendered on top
    if compositions:
        for comp in compositions:
            comp_id = comp if isinstance(comp, str) else comp.get('id', '')
            if comp_id:
                comp_pascal = to_pascal_case(comp_id)
                lines.append(f'      <{comp_pascal} />')
    elif not has_flat_file and not has_veo_clip:
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
    """Generate the Root.tsx content that registers all section compositions
    and individual component compositions for preview."""
    lines: List[str] = []

    lines.append('import React from "react";')
    lines.append('import { Composition } from "remotion";')
    lines.append('')

    # Import all section components (always from wrapper directory)
    for section in sections:
        section_id = section['id']
        pascal_name = to_pascal_case(section_id)
        component_name = f'{pascal_name}Section'
        lines.append(f'import {{ {component_name} }} from "./{section_id}";')

    # Import individual components for preview compositions
    all_comp_ids: List[str] = []
    for section in sections:
        compositions = section.get('compositions', [])
        for comp in compositions:
            comp_id = comp if isinstance(comp, str) else comp.get('id', '')
            if comp_id and comp_id not in all_comp_ids:
                comp_pascal = to_pascal_case(comp_id)
                lines.append(f'import {{ {comp_pascal} }} from "./{comp_id}";')
                all_comp_ids.append(comp_id)

    lines.append('')
    lines.append('const PREVIEW_DURATION = 150; // 5s at 30fps')
    lines.append('')
    lines.append('export const RemotionRoot: React.FC = () => {')
    lines.append('  return (')
    lines.append('    <>')

    # Section-level compositions
    for section in sections:
        section_id = section['id']
        pascal_name = to_pascal_case(section_id)
        component_name = f'{pascal_name}Section'
        composition_id = section.get('compositionId', pascal_name + 'Section')
        duration_seconds = section.get('durationSeconds', 0)
        duration_frames = math.ceil(duration_seconds * fps)
        width = section.get('width', 1920)
        height = section.get('height', 1080)

        lines.append(f'      <Composition')
        lines.append(f'        id="{composition_id}"')
        lines.append(f'        component={{{component_name}}}')
        lines.append(f'        durationInFrames={{{duration_frames}}}')
        lines.append(f'        fps={{{fps}}}')
        lines.append(f'        width={{{width}}}')
        lines.append(f'        height={{{height}}}')
        lines.append(f'      />')

    # Individual component compositions (for preview rendering)
    # Remotion composition IDs cannot contain underscores — use hyphens.
    registered: set = set()
    for section in sections:
        compositions = section.get('compositions', [])
        width = section.get('width', 1920)
        height = section.get('height', 1080)
        for comp in compositions:
            comp_id = comp if isinstance(comp, str) else comp.get('id', '')
            if comp_id and comp_id not in registered:
                comp_pascal = to_pascal_case(comp_id)
                remotion_id = comp_id.replace('_', '-')
                lines.append(f'      <Composition')
                lines.append(f'        id="{remotion_id}"')
                lines.append(f'        component={{{comp_pascal}}}')
                lines.append(f'        durationInFrames={{PREVIEW_DURATION}}')
                lines.append(f'        fps={{{fps}}}')
                lines.append(f'        width={{{width}}}')
                lines.append(f'        height={{{height}}}')
                lines.append(f'      />')
                registered.add(comp_id)

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

    # Always regenerate Root.tsx from scratch to ensure all section and
    # individual component compositions are correctly registered.
    new_content = generate_root_tsx(sections, fps, remotion_dir)

    with open(root_path, 'w', encoding='utf-8') as f:
        f.write(new_content)


def _merge_root_tsx(
    existing_content: str,
    sections: List[Dict[str, Any]],
    fps: int,
    remotion_dir: str = '',
) -> str:
    """Merge section compositions into an existing Root.tsx file.

    Uses regex to find existing <Composition> blocks and replace/append
    section entries. Also ensures imports are present.
    """
    content = existing_content

    # Build the set of section imports and compositions we need
    import_lines: List[str] = []
    composition_lines: List[str] = []
    remotion_src = os.path.join(remotion_dir, 'src', 'remotion') if remotion_dir else ''

    for section in sections:
        section_id = section['id']
        pascal_name = to_pascal_case(section_id)
        component_name = f'{pascal_name}Section'
        composition_id = section.get('compositionId', pascal_name + 'Section')
        duration_seconds = section.get('durationSeconds', 0)
        duration_frames = math.ceil(duration_seconds * fps)
        width = section.get('width', 1920)
        height = section.get('height', 1080)

        import_line = f'import {{ {component_name} }} from "./{section_id}";'
        import_lines.append(import_line)

        comp_block = (
            f'      <Composition\n'
            f'        id="{composition_id}"\n'
            f'        component={{{component_name}}}\n'
            f'        durationInFrames={{{duration_frames}}}\n'
            f'        fps={{{fps}}}\n'
            f'        width={{{width}}}\n'
            f'        height={{{height}}}\n'
            f'      />'
        )
        composition_lines.append(comp_block)

    # Individual component compositions (for preview rendering)
    registered_comps: set = set()
    for section in sections:
        compositions = section.get('compositions', [])
        width = section.get('width', 1920)
        height = section.get('height', 1080)
        for comp in compositions:
            comp_id = comp if isinstance(comp, str) else comp.get('id', '')
            if comp_id and comp_id not in registered_comps:
                comp_pascal = to_pascal_case(comp_id)
                import_line = f'import {{ {comp_pascal} }} from "./{comp_id}";'
                import_lines.append(import_line)
                remotion_id = comp_id.replace('_', '-')
                comp_block = (
                    f'      <Composition\n'
                    f'        id="{remotion_id}"\n'
                    f'        component={{{comp_pascal}}}\n'
                    f'        durationInFrames={{150}}\n'
                    f'        fps={{{fps}}}\n'
                    f'        width={{{width}}}\n'
                    f'        height={{{height}}}\n'
                    f'      />'
                )
                composition_lines.append(comp_block)
                registered_comps.add(comp_id)

    # Remove existing section and component imports (lines importing from ./...)
    section_ids = {s['id'] for s in sections}
    # Also track individual component IDs for import/composition removal
    all_comp_ids = set()
    for s in sections:
        for comp in s.get('compositions', []):
            comp_id = comp if isinstance(comp, str) else comp.get('id', '')
            if comp_id:
                all_comp_ids.add(comp_id)
    removable_ids = section_ids | all_comp_ids
    existing_lines = content.split('\n')
    filtered_lines: List[str] = []
    for line in existing_lines:
        # Check if this line is an import for one of our sections or components
        import_match = re.match(r'import\s+\{.*\}\s+from\s+["\']\.\/(\w[\w\-]*)["\']\s*;', line)
        if import_match and import_match.group(1) in removable_ids:
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

    # Remove existing <Composition> blocks for our section IDs, compositionIds,
    # and individual component IDs
    ids_to_remove: set = set()
    for section in sections:
        section_id = section['id']
        pascal_name = to_pascal_case(section_id)
        composition_id = section.get('compositionId', pascal_name + 'Section')
        ids_to_remove.add(section_id)
        ids_to_remove.add(composition_id)
    ids_to_remove |= all_comp_ids
    # Also remove hyphenated versions of component IDs
    ids_to_remove |= {cid.replace('_', '-') for cid in all_comp_ids}

    for remove_id in ids_to_remove:
            # Match <Composition ... id="remove_id" ... /> (possibly multiline)
            pattern = re.compile(
                r'\s*<Composition\s[^>]*id=["\']' + re.escape(remove_id) + r'["\'][^>]*/>\s*',
                re.DOTALL
            )
            # Also handle multi-line Composition blocks
            pattern_multiline = re.compile(
                r'\s*<Composition\s*\n(?:\s+\S+.*\n)*?\s+id=["\']' + re.escape(remove_id) + r'["\'].*?\n(?:\s+\S+.*\n)*?\s*/>\s*',
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
        remotion_public = os.path.join(remotion_dir, 'public')
        remotion_src = os.path.join(remotion_dir, 'src', 'remotion')
        tsx_content = generate_section_component(section, fps, remotion_public, remotion_src=remotion_src)

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