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
import shutil
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


def resolve_comp_import(comp_id: str, section_id: str, remotion_src: str) -> tuple:
    """Resolve the JS identifier and import path for a composition.

    Digit-prefixed PascalCase names are invalid JS identifiers, so we prefix
    them with the section's PascalCase name. We then check the filesystem
    to find the correct import path.

    Returns:
        (js_identifier, import_path) e.g. ("Part1Economics07StatCalloutGitclear", "Part1Economics07StatCalloutGitclear")
    """
    comp_pascal = to_pascal_case(comp_id)
    section_pascal = to_pascal_case(section_id)

    # If PascalCase starts with a digit, prefix with section PascalCase
    if comp_pascal and comp_pascal[0].isdigit():
        comp_pascal = section_pascal + comp_pascal

    # Resolve the import path by checking filesystem in priority order
    if remotion_src:
        # 1. PascalCase directory (e.g. Part1Economics07StatCalloutGitclear/)
        pascal_dir = os.path.join(remotion_src, comp_pascal)
        if os.path.isdir(pascal_dir):
            return (comp_pascal, comp_pascal)

        # 2. Kebab-style directory (e.g. 07-StatCalloutGitclear/)
        # Build kebab from comp_id: "07_stat_callout_gitclear" -> "07-StatCalloutGitclear"
        parts = re.split(r'[_\-]', comp_id)
        kebab_name = parts[0] + '-' + ''.join(p.capitalize() for p in parts[1:] if p) if len(parts) > 1 else comp_id
        kebab_dir = os.path.join(remotion_src, kebab_name)
        if os.path.isdir(kebab_dir):
            return (comp_pascal, kebab_name)

        # 3. Flat file (e.g. 07_stat_callout_gitclear.tsx)
        flat_file = os.path.join(remotion_src, f'{comp_id}.tsx')
        if os.path.isfile(flat_file):
            return (comp_pascal, comp_id)

    # Fallback: use comp_id as import path
    return (comp_pascal, comp_id)


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


STATIC_FILE_RE = re.compile(r'staticFile\(\s*["\']([^"\']+)["\']\s*\)')
AUDIO_EXTENSIONS = {'.wav', '.mp3', '.aac', '.m4a', '.ogg'}
VIDEO_EXTENSIONS = {'.mp4', '.webm', '.mov', '.m4v'}


def _read_text_if_exists(path: str) -> str:
    """Return file contents when the file exists and is readable."""
    try:
        with open(path, 'r', encoding='utf-8') as f:
            return f.read()
    except OSError:
        return ''


def _existing_static_path(remotion_public: str, candidates: List[str]) -> Optional[str]:
    """Return the first staticFile() path that exists under remotion/public."""
    if not remotion_public:
        return None

    for rel_path in candidates:
        if os.path.isfile(os.path.join(remotion_public, rel_path)):
            return rel_path
    return None


def ensure_section_asset_aliases(section_id: str, remotion_public: str) -> None:
    """Create compatibility aliases for common Claude-generated staticFile paths.

    We keep the canonical staged asset locations:
      - {section_id}/narration.wav
      - veo/{section_id}.mp4

    But Claude-generated section compositions commonly drift to these variants:
      - {section_id}_narration.wav
      - {section_id}.mp4

    Creating aliases here makes wrapper generation and final render tolerant to
    those variations without relying on Claude to be perfectly deterministic.
    """
    if not remotion_public:
        return

    canonical_audio = os.path.join(remotion_public, section_id, 'narration.wav')
    audio_alias = os.path.join(remotion_public, f'{section_id}_narration.wav')
    if os.path.isfile(canonical_audio) and not os.path.isfile(audio_alias):
        os.makedirs(os.path.dirname(audio_alias), exist_ok=True)
        shutil.copy2(canonical_audio, audio_alias)

    for ext in ['.mp4', '.webm', '.mov', '.m4v']:
        canonical_video = os.path.join(remotion_public, 'veo', f'{section_id}{ext}')
        video_alias = os.path.join(remotion_public, f'{section_id}{ext}')
        if os.path.isfile(canonical_video) and not os.path.isfile(video_alias):
            os.makedirs(os.path.dirname(video_alias), exist_ok=True)
            shutil.copy2(canonical_video, video_alias)


def resolve_direct_audio_src(section_id: str, remotion_public: str) -> Optional[str]:
    """Resolve the canonical/compatible narration asset for wrapper use."""
    return _existing_static_path(
        remotion_public,
        [
            f'{section_id}/narration.wav',
            f'{section_id}_narration.wav',
        ],
    )


def resolve_direct_video_src(section_id: str, remotion_public: str) -> Optional[str]:
    """Resolve the canonical/compatible Veo asset for wrapper use."""
    candidates: List[str] = []
    for ext in ['.mp4', '.webm', '.mov', '.m4v']:
        candidates.extend([
            f'veo/{section_id}{ext}',
            f'{section_id}{ext}',
        ])
    return _existing_static_path(remotion_public, candidates)


def detect_component_media(
    source: str,
    remotion_public: str,
) -> Dict[str, bool]:
    """Detect whether a component already owns working audio/video media refs."""
    refs = STATIC_FILE_RE.findall(source)
    has_audio_tag = 'Audio' in source
    has_video_tag = 'OffthreadVideo' in source

    audio_refs = [
        ref for ref in refs if Path(ref).suffix.lower() in AUDIO_EXTENSIONS
    ]
    video_refs = [
        ref for ref in refs if Path(ref).suffix.lower() in VIDEO_EXTENSIONS
    ]

    has_audio = has_audio_tag and any(
        os.path.isfile(os.path.join(remotion_public, ref))
        for ref in audio_refs
    )
    has_video = has_video_tag and any(
        os.path.isfile(os.path.join(remotion_public, ref))
        for ref in video_refs
    )

    return {
        'has_audio': has_audio,
        'has_video': has_video,
    }


def resolve_section_base_component(
    section: Dict[str, Any],
    remotion_src: str,
) -> Optional[tuple[str, str, str]]:
    """Resolve an authored section-level component to delegate wrapper rendering.

    Priority order:
    1. Section-local composition file: {section_id}/{compositionId}.tsx
    2. Section-local wrapper-named file: {section_id}/{SectionPascal}Section.tsx
    3. Top-level composition file: {compositionId}.tsx
    4. Top-level wrapper-named file: {SectionPascal}Section.tsx

    Section-local files take precedence because they contain the authored timing
    logic for the full section. Falling back to top-level files preserves the
    prior "flat section file" behavior for Claude-generated outputs.
    """
    if not remotion_src:
        return None

    section_id = section['id']
    section_pascal = to_pascal_case(section_id)
    component_name = f'{section_pascal}Section'
    composition_id = section.get('compositionId', component_name)

    candidates = [
        (
            composition_id,
            os.path.join(remotion_src, section_id, f'{composition_id}.tsx'),
            f'./{composition_id}',
        ),
        (
            component_name,
            os.path.join(remotion_src, section_id, f'{component_name}.tsx'),
            f'./{component_name}',
        ),
        (
            composition_id,
            os.path.join(remotion_src, f'{composition_id}.tsx'),
            f'../{composition_id}',
        ),
        (
            component_name,
            os.path.join(remotion_src, f'{component_name}.tsx'),
            f'../{component_name}',
        ),
    ]

    for export_name, abs_path, import_path in candidates:
        if os.path.isfile(abs_path):
            return (export_name, import_path, abs_path)

    return None


def _collapse_whitespace(value: str) -> str:
    """Normalize whitespace to simplify loose section matching."""
    return re.sub(r'\s+', ' ', value).strip()


def normalize_section_intent_key(value: str) -> str:
    """Normalize section text for script-heading matching."""
    return _collapse_whitespace(
        re.sub(
            r'[^a-z0-9\s]',
            ' ',
            re.sub(
                r'([0-9])([a-z])',
                r'\1 \2',
                re.sub(
                    r'([a-z])([0-9])',
                    r'\1 \2',
                    re.sub(r'[_\-]+', ' ', value.lower()),
                ),
            ),
        )
    )


def parse_script_section_visual_intent(content: str) -> List[Dict[str, Any]]:
    """Parse main_script.md into section blocks and capture [veo:] markers."""
    sections: List[Dict[str, Any]] = []
    current: Optional[Dict[str, Any]] = None

    for raw_line in content.splitlines():
        line = raw_line.strip()
        if re.match(r'^##\s+', line):
            if current is not None:
                sections.append(current)
            heading = re.sub(r'^##\s+', '', line).strip()
            current = {
                'heading': heading,
                'normalized_heading': normalize_section_intent_key(heading),
                'veo_markers': [],
            }
            continue

        if current is None:
            continue

        for match in re.finditer(r'\[veo:\s*([^\]]*?)\]', line, re.IGNORECASE):
            current['veo_markers'].append((match.group(1) or '').strip())

    if current is not None:
        sections.append(current)

    return [section for section in sections if section['heading']]


def _build_section_intent_candidates(section: Dict[str, Any]) -> List[str]:
    """Build normalized candidate names for a project section."""
    label = str(section.get('label') or '')
    section_id = str(section.get('id') or '')
    variants = [
        label,
        section_id,
        re.sub(r'^part\s+\d+\s*:\s*', '', label, flags=re.IGNORECASE),
        re.sub(r'^part[_\-]?(\d+)[_\-]?', r'part \1 ', section_id, flags=re.IGNORECASE),
    ]
    normalized = [normalize_section_intent_key(variant) for variant in variants if variant]
    seen = set()
    unique: List[str] = []
    for variant in normalized:
        if variant and variant not in seen:
            seen.add(variant)
            unique.append(variant)
    return unique


def _token_overlap_score(left: str, right: str) -> float:
    """Score loose heading matches by overlapping normalized tokens."""
    left_tokens = [token for token in left.split(' ') if token]
    right_tokens = [token for token in right.split(' ') if token]
    if not left_tokens or not right_tokens:
        return 0.0
    right_set = set(right_tokens)
    overlap = sum(1 for token in left_tokens if token in right_set)
    return overlap / max(len(left_tokens), len(right_tokens))


def find_matching_script_section_visual_intent(
    script_sections: List[Dict[str, Any]],
    section: Dict[str, Any],
) -> Optional[Dict[str, Any]]:
    """Find the best-matching script heading for a project section."""
    candidates = _build_section_intent_candidates(section)
    best_section: Optional[Dict[str, Any]] = None
    best_score = 0

    for script_section in script_sections:
        for candidate in candidates:
            normalized_heading = script_section['normalized_heading']
            condensed_heading = re.sub(r'\s+', '', normalized_heading)
            condensed_candidate = re.sub(r'\s+', '', candidate)

            if normalized_heading == candidate:
                score = 100
            elif condensed_heading == condensed_candidate:
                score = 95
            elif normalized_heading in candidate or candidate in normalized_heading:
                score = 80
            else:
                score = round(_token_overlap_score(normalized_heading, candidate) * 70)

            if score > best_score:
                best_score = score
                best_section = script_section

    return best_section if best_score >= 60 else None


def resolve_section_has_veo_intent(
    section: Dict[str, Any],
    project_dir: str,
) -> Optional[bool]:
    """Return whether the matched script section explicitly uses [veo:]."""
    if not project_dir:
        return None

    main_script_path = os.path.join(project_dir, 'narrative', 'main_script.md')
    script_content = _read_text_if_exists(main_script_path)
    if not script_content:
        return None

    matching_section = find_matching_script_section_visual_intent(
        parse_script_section_visual_intent(script_content),
        section,
    )
    if matching_section is None:
        return None

    return any(marker for marker in matching_section['veo_markers'])


def generate_generated_timeline_wrapper(
    section: Dict[str, Any],
    fps: int,
    needs_direct_audio: bool,
    needs_direct_video: bool,
    direct_audio_src: Optional[str],
    direct_video_src: Optional[str],
    remotion_src: str,
) -> Optional[str]:
    """Generate a deterministic wrapper for Stage 8-generated section timelines.

    Claude can generate component files and constants nondeterministically, but
    the final section wrapper must remain deterministic. When Stage 8 marks a
    section timeline as generated and constants.ts exists, we render the active
    visual directly from VISUAL_SEQUENCE using exact filesystem-resolved imports.
    """
    section_id = section['id']
    if section.get('timelineSource') != 'generated' or not remotion_src:
        return None

    constants_path = os.path.join(remotion_src, section_id, 'constants.ts')
    if not os.path.isfile(constants_path):
        return None

    pascal_name = to_pascal_case(section_id)
    component_name = f'{pascal_name}Section'
    duration_seconds = section.get('durationSeconds', 0)
    compositions: List[Dict[str, Any]] = section.get('compositions', [])

    resolved_components: List[tuple[str, str, str]] = []
    for comp in compositions:
        comp_id = comp if isinstance(comp, str) else comp.get('id', '')
        if not comp_id or comp_id.startswith('veo:'):
            continue
        comp_pascal, import_path = resolve_comp_import(comp_id, section_id, remotion_src)
        resolved_components.append((comp_id, comp_pascal, import_path))

    remotion_imports = ['Sequence', 'useCurrentFrame']
    if needs_direct_audio:
        remotion_imports.append('Audio')
    if needs_direct_video:
        remotion_imports.append('OffthreadVideo')
    if needs_direct_audio or needs_direct_video:
        remotion_imports.append('staticFile')

    lines: List[str] = []
    lines.append('import React from "react";')
    lines.append(f'import {{ {", ".join(remotion_imports)} }} from "remotion";')
    lines.append('import { VISUAL_SEQUENCE } from "./constants";')

    for _, comp_pascal, import_path in resolved_components:
        lines.append(f'import {{ {comp_pascal} }} from "../{import_path}";')

    lines.append('')
    lines.append('const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {')
    for comp_id, comp_pascal, _ in resolved_components:
        lines.append(f'  "{comp_id}": {comp_pascal},')
    lines.append('};')
    lines.append('')
    lines.append(f'export const {component_name}: React.FC = () => {{')
    lines.append(f'  const fps = {fps};')
    lines.append(f'  const durationSeconds = {duration_seconds};')
    lines.append('  const frame = useCurrentFrame();')
    lines.append('  let activeVisual = VISUAL_SEQUENCE.length > 0 ? VISUAL_SEQUENCE[0] : null;')
    lines.append('  for (let i = VISUAL_SEQUENCE.length - 1; i >= 0; i--) {')
    lines.append('    if (frame >= VISUAL_SEQUENCE[i].start) {')
    lines.append('      activeVisual = VISUAL_SEQUENCE[i];')
    lines.append('      break;')
    lines.append('    }')
    lines.append('  }')
    lines.append('  const ActiveComponent = activeVisual ? COMPONENT_MAP[activeVisual.id] ?? null : null;')
    lines.append('')
    lines.append('  return (')
    lines.append('    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>')
    if needs_direct_audio and direct_audio_src is not None:
        lines.append(f'      <Audio src={{staticFile("{direct_audio_src}")}} />')
    if needs_direct_video and direct_video_src is not None:
        lines.append(f'      <OffthreadVideo src={{staticFile("{direct_video_src}")}} style={{{{ width: "100%", height: "100%" }}}} />')
    lines.append('      {ActiveComponent && activeVisual ? (')
    lines.append('        <Sequence')
    lines.append('          from={activeVisual.start}')
    lines.append('          durationInFrames={Math.max(1, activeVisual.end - activeVisual.start)}')
    lines.append('        >')
    lines.append('          <ActiveComponent />')
    lines.append('        </Sequence>')
    lines.append('      ) : null}')
    lines.append('    </Sequence>')
    lines.append('  );')
    lines.append('};')
    lines.append('')
    lines.append(f'export default {component_name};')
    lines.append('')

    return '\n'.join(lines)


def get_fps(project_data: Dict[str, Any]) -> int:
    """Extract FPS from project.json render config, defaulting to 30."""
    render_config = project_data.get('render', {})
    return int(render_config.get('fps', 30))


def generate_section_component(
    section: Dict[str, Any],
    fps: int,
    remotion_public: str = '',
    remotion_src: str = '',
    project_dir: str = '',
) -> str:
    """Generate the TSX source code for a section wrapper component.

    When an authored section-level composition exists, the wrapper delegates to
    it and does not re-mount child compositions on top. This avoids double-
    rendering the full section, which otherwise causes every animation layer to
    appear simultaneously over the Veo clip.
    """
    section_id = section['id']
    pascal_name = to_pascal_case(section_id)
    component_name = f'{pascal_name}Section'
    duration_seconds = section.get('durationSeconds', 0)
    offset_seconds = section.get('offsetSeconds', 0)
    compositions: List[Dict[str, Any]] = section.get('compositions', [])

    ensure_section_asset_aliases(section_id, remotion_public)

    base_component = resolve_section_base_component(section, remotion_src)
    has_base_component = base_component is not None
    component_has_audio = False
    component_has_video = False
    if has_base_component and base_component is not None and remotion_public:
        _, _, component_abs_path = base_component
        media = detect_component_media(
            _read_text_if_exists(component_abs_path),
            remotion_public,
        )
        component_has_audio = media['has_audio']
        component_has_video = media['has_video']

    # Detect available assets in remotion/public/ (only when NOT delegating)
    direct_audio_src = resolve_direct_audio_src(section_id, remotion_public)
    direct_video_src = resolve_direct_video_src(section_id, remotion_public)
    has_veo_intent = resolve_section_has_veo_intent(section, project_dir)
    needs_direct_audio = bool(direct_audio_src) and (not has_base_component or not component_has_audio)
    needs_direct_video = (
        bool(direct_video_src)
        and (not has_base_component or not component_has_video)
        and has_veo_intent is not False
    )

    generated_timeline_wrapper = generate_generated_timeline_wrapper(
        section,
        fps,
        needs_direct_audio,
        needs_direct_video,
        direct_audio_src,
        direct_video_src,
        remotion_src,
    )
    if generated_timeline_wrapper is not None:
        return generated_timeline_wrapper

    lines: List[str] = []

    # Imports
    remotion_imports = ['Sequence']
    if needs_direct_audio:
        remotion_imports.append('Audio')
    if needs_direct_video:
        remotion_imports.append('OffthreadVideo')
    if needs_direct_audio or needs_direct_video:
        remotion_imports.append('staticFile')

    lines.append('import React from "react";')
    lines.append(f'import {{ {", ".join(remotion_imports)} }} from "remotion";')
    lines.append('')

    # Import authored section component as Base when delegating
    if has_base_component and base_component is not None:
        export_name, import_path, _ = base_component
        lines.append(
            f'import {{ {export_name} as {component_name}Base }} from "{import_path}";'
        )

    # Import sub-compositions if present
    remotion_src_dir = remotion_src or ''
    if compositions and not has_base_component:
        for comp in compositions:
            comp_id = comp if isinstance(comp, str) else comp.get('id', '')
            if comp_id:
                comp_pascal, import_path = resolve_comp_import(comp_id, section_id, remotion_src_dir)
                lines.append(f'import {{ {comp_pascal} }} from "../{import_path}";')

    if has_base_component or (compositions and not has_base_component):
        lines.append('')

    # Component definition
    lines.append(f'export const {component_name}: React.FC = () => {{')
    lines.append(f'  const fps = {fps};')
    lines.append(f'  const offsetSeconds = {offset_seconds};')
    lines.append(f'  const durationSeconds = {duration_seconds};')
    lines.append('')
    lines.append('  return (')
    lines.append(f'    <Sequence from={{0}} durationInFrames={{Math.ceil(durationSeconds * fps)}}>')

    # Render missing direct assets first so the authored component can overlay them.
    if needs_direct_audio and direct_audio_src is not None:
        lines.append(f'      <Audio src={{staticFile("{direct_audio_src}")}} />')
    if needs_direct_video and direct_video_src is not None:
        lines.append(f'      <OffthreadVideo src={{staticFile("{direct_video_src}")}} style={{{{ width: "100%", height: "100%" }}}} />')

    if has_base_component:
        # Delegate to the authored section composition for timing / orchestration.
        lines.append(f'      <{component_name}Base />')

    # Sub-compositions rendered on top
    if compositions and not has_base_component:
        for comp in compositions:
            comp_id = comp if isinstance(comp, str) else comp.get('id', '')
            start_seconds = comp.get('startSeconds') if isinstance(comp, dict) else None
            comp_duration = comp.get('durationSeconds') if isinstance(comp, dict) else None
            if comp_id:
                comp_pascal, _ = resolve_comp_import(comp_id, section_id, remotion_src_dir)
                if start_seconds is not None and comp_duration is not None:
                    lines.append(f'      <Sequence from={{Math.round({start_seconds} * fps)}} durationInFrames={{Math.ceil({comp_duration} * fps)}}>')
                    lines.append(f'        <{comp_pascal} />')
                    lines.append(f'      </Sequence>')
                else:
                    lines.append(f'      <{comp_pascal} />')
    elif not has_base_component and not needs_direct_video:
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
    remotion_src = os.path.join(remotion_dir, 'src', 'remotion') if remotion_dir else ''
    imported_pascals: set = set()
    for section in sections:
        section_id = section['id']
        compositions = section.get('compositions', [])
        for comp in compositions:
            comp_id = comp if isinstance(comp, str) else comp.get('id', '')
            if comp_id:
                comp_pascal, import_path = resolve_comp_import(comp_id, section_id, remotion_src)
                if comp_pascal not in imported_pascals:
                    lines.append(f'import {{ {comp_pascal} }} from "./{import_path}";')
                    imported_pascals.add(comp_pascal)

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
        section_id = section['id']
        compositions = section.get('compositions', [])
        width = section.get('width', 1920)
        height = section.get('height', 1080)
        for comp in compositions:
            comp_id = comp if isinstance(comp, str) else comp.get('id', '')
            if comp_id:
                comp_pascal, _ = resolve_comp_import(comp_id, section_id, remotion_src)
                if comp_pascal in registered:
                    continue
                # Use hyphenated comp_pascal as the Remotion composition ID
                # to ensure uniqueness across sections
                remotion_id = re.sub(r'([a-z0-9])([A-Z])', r'\1-\2', comp_pascal).lower()
                lines.append(f'      <Composition')
                lines.append(f'        id="{remotion_id}"')
                lines.append(f'        component={{{comp_pascal}}}')
                lines.append(f'        durationInFrames={{PREVIEW_DURATION}}')
                lines.append(f'        fps={{{fps}}}')
                lines.append(f'        width={{{width}}}')
                lines.append(f'        height={{{height}}}')
                lines.append(f'      />')
                registered.add(comp_pascal)

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
        section_id = section['id']
        compositions = section.get('compositions', [])
        width = section.get('width', 1920)
        height = section.get('height', 1080)
        for comp in compositions:
            comp_id = comp if isinstance(comp, str) else comp.get('id', '')
            if comp_id:
                comp_pascal, import_path = resolve_comp_import(comp_id, section_id, remotion_src)
                if comp_pascal in registered_comps:
                    continue
                import_line = f'import {{ {comp_pascal} }} from "./{import_path}";'
                import_lines.append(import_line)
                remotion_id = re.sub(r'([a-z0-9])([A-Z])', r'\1-\2', comp_pascal).lower()
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
                registered_comps.add(comp_pascal)

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
            # Remove <Composition ... id="remove_id" ... /> blocks (single or multi-line)
            # Uses atomic-style matching via line-by-line approach to avoid catastrophic backtracking.
            escaped_id = re.escape(remove_id)
            id_pattern = re.compile(r'id=["\']' + escaped_id + r'["\']')
            content_lines = content.split('\n')
            filtered: List[str] = []
            i = 0
            while i < len(content_lines):
                line = content_lines[i]
                # Detect start of a <Composition block
                if '<Composition' in line:
                    # Collect the full block (until we find />)
                    block_lines = [line]
                    j = i
                    while '/>' not in content_lines[j] and j < len(content_lines) - 1:
                        j += 1
                        block_lines.append(content_lines[j])
                    block_text = '\n'.join(block_lines)
                    if id_pattern.search(block_text):
                        # Skip this entire Composition block
                        i = j + 1
                        continue
                filtered.append(content_lines[i])
                i += 1
            content = '\n'.join(filtered)

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
        tsx_content = generate_section_component(
            section,
            fps,
            remotion_public,
            remotion_src=remotion_src,
            project_dir=project_dir,
        )

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
