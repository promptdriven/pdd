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
from datetime import datetime, timezone
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
IMAGE_EXTENSIONS = {'.png', '.jpg', '.jpeg', '.webp'}
NON_COMPONENT_BASENAMES = {'spec', 'veo'}
VISUAL_MEDIA_KEY_RE = re.compile(
    r'(?:"|\b)(leftClip|rightClip|clipSource|leftSrc|rightSrc|outputSrc|outputFile|filename|backgroundClip|backgroundSrc|baseClip|baseSrc|revealClip|revealSrc)(?:"|\b)\s*[:=]\s*["\']([^"\']+\.(?:mp4|webm|mov|m4v))["\']',
    re.IGNORECASE,
)
STRUCTURED_VIDEO_FIELD_RE = re.compile(
    r'(?:"|\b)(outputFile|filename|clip_id|clipId)(?:"|\b)\s*[:=]\s*["\']([^"\']+)["\']',
    re.IGNORECASE,
)
GENERIC_VIDEO_REF_RE = re.compile(
    r'(?:"|\b)(video|src)\s*[:=]\s*["\']([^"\']+\.(?:mp4|webm|mov|m4v))["\']',
    re.IGNORECASE,
)
DATA_POINTS_JSON_RE = re.compile(
    r'##\s*Data Points\s*```json\s*([\s\S]+?)\s*```',
    re.IGNORECASE,
)
NARRATION_SYNC_RE = re.compile(
    r'##\s*Narration Sync\s*(?:\r?\n)+>\s*"([^"\n]+)"',
    re.IGNORECASE,
)
NARRATION_JSON_RE = re.compile(
    r'"narration"\s*:\s*"([^"\n]+)"',
    re.IGNORECASE,
)
VIDEO_EXTENSION_PRIORITY = ('.mp4', '.webm', '.mov', '.m4v')
MEDIA_ALIAS_KEY_MAP = {
    'clipsource': 'defaultSrc',
    'leftclip': 'leftSrc',
    'leftsrc': 'leftSrc',
    'rightclip': 'rightSrc',
    'rightsrc': 'rightSrc',
    'outputsrc': 'outputSrc',
    'outputfile': 'defaultSrc',
    'filename': 'defaultSrc',
    'backgroundclip': 'backgroundSrc',
    'backgroundsrc': 'backgroundSrc',
    'baseclip': 'baseSrc',
    'basesrc': 'baseSrc',
    'revealclip': 'revealSrc',
    'revealsrc': 'revealSrc',
    'videosrc': 'defaultSrc',
}
PANEL_CONTEXT_ALIAS_MAP = {
    'left': 'leftSrc',
    'leftpanel': 'leftSrc',
    'before': 'leftSrc',
    'beforepanel': 'leftSrc',
    'right': 'rightSrc',
    'rightpanel': 'rightSrc',
    'after': 'rightSrc',
    'afterpanel': 'rightSrc',
    'background': 'backgroundSrc',
    'base': 'baseSrc',
}
SOURCE_FIELD_KEYS = {
    'source',
    'sourcefile',
    'videosource',
    'videosrc',
    'video',
    'file',
    'asset',
    'assetfile',
    'clip',
}
REFERENCE_SUFFIXES = (
    '_still',
    '-still',
    '_frame',
    '-frame',
    '_image',
    '-image',
    '_poster',
    '-poster',
    '_thumbnail',
    '-thumbnail',
)


def _read_text_if_exists(path: str) -> str:
    """Return file contents when the file exists and is readable."""
    try:
        with open(path, 'r', encoding='utf-8') as f:
            return f.read()
    except OSError:
        return ''


def _extract_data_points_json(spec_content: str) -> Optional[Any]:
    """Return parsed JSON from the spec's Data Points block when present."""
    match = DATA_POINTS_JSON_RE.search(spec_content)
    if not match:
        return None

    try:
        return json.loads(match.group(1))
    except json.JSONDecodeError:
        return None


def _is_video_reference(value: str) -> bool:
    return Path(value).suffix.lower() in VIDEO_EXTENSIONS


def _is_media_reference_like(value: str) -> bool:
    suffix = Path(value).suffix.lower()
    return suffix in VIDEO_EXTENSIONS or suffix in IMAGE_EXTENSIONS


def _normalize_reference_stems(raw_value: str) -> List[str]:
    normalized = raw_value.replace('\\', '/').lstrip('/')
    if not normalized:
        return []

    basename = normalized.split('/')[-1]
    basename_stem = Path(basename).stem
    normalized_stem = str(Path(normalized))
    if Path(normalized_stem).suffix:
        normalized_stem = str(Path(normalized_stem).with_suffix(''))

    candidates: List[str] = []

    def _add(candidate: str) -> None:
        trimmed = candidate.strip().strip('/').replace('\\', '/')
        if trimmed and trimmed not in candidates:
            candidates.append(trimmed)

    for candidate in (normalized, basename, normalized_stem, basename_stem):
        _add(candidate)

    for suffix in REFERENCE_SUFFIXES:
        for candidate in list(candidates):
            if candidate.endswith(suffix):
                _add(candidate[: -len(suffix)])

    return candidates


def _iter_data_point_media_values(data_points: Any) -> List[str]:
    """Collect media-like string values inside structured Data Points JSON."""
    values: List[str] = []

    def _walk(value: Any, key_hint: Optional[str] = None) -> None:
        if isinstance(value, dict):
            for raw_key, nested in value.items():
                _walk(nested, str(raw_key).strip().lower().replace('_', '').replace('-', ''))
            return
        if isinstance(value, list):
            for nested in value:
                _walk(nested, key_hint)
            return
        if isinstance(value, str) and (
            _is_media_reference_like(value) or (key_hint in SOURCE_FIELD_KEYS and value.strip())
        ):
            normalized = value.replace('\\', '/').lstrip('/')
            if normalized not in values:
                values.append(normalized)

    _walk(data_points)
    return values


def _extract_data_point_media_aliases(
    data_points: Any,
    remotion_public: str,
    reference_aliases: Optional[Dict[str, str]] = None,
) -> Dict[str, str]:
    """Resolve structured media aliases from Data Points JSON."""
    aliases: Dict[str, str] = {}

    def _assign(alias_name: Optional[str], raw_value: str) -> None:
        resolved = _resolve_video_reference_static_path(
            remotion_public,
            raw_value,
            reference_aliases,
        )
        if resolved is None:
            return
        if alias_name:
            aliases.setdefault(alias_name, resolved)
        aliases.setdefault('defaultSrc', resolved)

    def _walk(value: Any, context_alias: Optional[str] = None) -> None:
        if isinstance(value, dict):
            for raw_key, nested in value.items():
                key = str(raw_key).strip().lower().replace('_', '').replace('-', '')
                next_context = PANEL_CONTEXT_ALIAS_MAP.get(key, context_alias)
                alias_name = MEDIA_ALIAS_KEY_MAP.get(key)
                if isinstance(nested, str) and (
                    _is_media_reference_like(nested) or (key in SOURCE_FIELD_KEYS and nested.strip())
                ):
                    effective_alias = next_context or alias_name
                    _assign(effective_alias, nested)
                    continue
                _walk(nested, next_context)
            return
        if isinstance(value, list):
            for nested in value:
                _walk(nested, context_alias)
            return
        if isinstance(value, str) and (
            _is_media_reference_like(value) or (context_alias is not None and value.strip())
        ):
            _assign(context_alias, value)

    _walk(data_points)
    return aliases


def _existing_static_path(remotion_public: str, candidates: List[str]) -> Optional[str]:
    """Return the first staticFile() path that exists under remotion/public."""
    if not remotion_public:
        return None

    for rel_path in candidates:
        if os.path.isfile(os.path.join(remotion_public, rel_path)):
            return rel_path
    return None


def component_base_name(component_id: str, section_id: str) -> str:
    """Normalize a composition id to the matching spec basename."""
    prefix = f'{section_id}_'
    return component_id[len(prefix):] if component_id.startswith(prefix) else component_id


def _list_section_spec_basenames(project_dir: str, section: Dict[str, Any]) -> List[str]:
    """List visual spec basenames for a section, excluding metadata specs."""
    if not project_dir:
        return []

    spec_dir = section.get('specDir') or section['id']
    if not os.path.isabs(spec_dir):
        spec_dir = os.path.join(project_dir, 'specs', str(spec_dir).replace('\\', '/').replace('specs/', '').strip('/'))

    if not os.path.isdir(spec_dir):
        return []

    basenames = []
    for entry in sorted(os.listdir(spec_dir)):
        if not entry.endswith('.md') or entry.startswith('AUDIT_'):
            continue
        base = os.path.splitext(entry)[0]
        if base in NON_COMPONENT_BASENAMES:
            continue
        basenames.append(base)
    return basenames


def _has_renderable_spec_media(
    project_dir: str,
    section: Dict[str, Any],
    spec_base: str,
    remotion_public: str = '',
) -> bool:
    """Return True when a spec-only visual has an explicit or staged media source."""
    if not project_dir:
        return False

    spec_dir = section.get('specDir') or section['id']
    if not os.path.isabs(spec_dir):
        spec_dir = os.path.join(project_dir, 'specs', str(spec_dir).replace('\\', '/').replace('specs/', '').strip('/'))

    spec_path = os.path.join(spec_dir, f'{spec_base}.md')
    if os.path.isfile(spec_path):
        spec_content = _read_text_if_exists(spec_path)
        if VISUAL_MEDIA_KEY_RE.search(spec_content):
            return True
        if STRUCTURED_VIDEO_FIELD_RE.search(spec_content):
            return True
        if GENERIC_VIDEO_REF_RE.search(spec_content):
            return True
        data_points = _extract_data_points_json(spec_content)
        if data_points is not None and _iter_data_point_media_values(data_points):
            return True
        for rel_path in STATIC_FILE_RE.findall(spec_content):
            if Path(rel_path).suffix.lower() in VIDEO_EXTENSIONS:
                return True

    staged_candidates = [
        os.path.join(project_dir, 'outputs', 'veo', f'{spec_base}{ext}')
        for ext in VIDEO_EXTENSION_PRIORITY
    ]
    if remotion_public:
        staged_candidates.extend(
            os.path.join(remotion_public, 'veo', f'{spec_base}{ext}')
            for ext in VIDEO_EXTENSION_PRIORITY
        )

    return any(os.path.isfile(candidate) for candidate in staged_candidates)


def resolve_section_visual_ids(
    section: Dict[str, Any],
    project_dir: str,
    remotion_public: str = '',
) -> List[str]:
    """Build the rendered visual order from spec files plus configured components."""
    compositions: List[Any] = section.get('compositions', [])
    composition_ids: List[str] = []
    for composition in compositions:
        comp_id = composition if isinstance(composition, str) else composition.get('id', '')
        if comp_id and comp_id not in composition_ids:
            composition_ids.append(comp_id)

    spec_basenames = _list_section_spec_basenames(project_dir, section)
    consumed: set[str] = set()
    visual_ids: List[str] = []

    for base in spec_basenames:
        matching = next(
            (
                comp_id
                for comp_id in composition_ids
                if component_base_name(comp_id, section['id']) == base
            ),
            None,
        )
        if matching is not None:
            visual_ids.append(matching)
            consumed.add(matching)
        elif _has_renderable_spec_media(project_dir, section, base, remotion_public):
            visual_ids.append(base)

    for comp_id in composition_ids:
        if comp_id not in consumed:
            visual_ids.append(comp_id)

    return visual_ids


def _resolve_media_static_path(remotion_public: str, rel_path: str) -> Optional[str]:
    """Return a media path only when the staged static asset exists."""
    normalized = rel_path.replace('\\', '/').lstrip('/')
    if not normalized:
        return None
    return normalized if os.path.isfile(os.path.join(remotion_public, normalized)) else None


def _resolve_video_reference_static_path(
    remotion_public: str,
    raw_value: str,
    reference_aliases: Optional[Dict[str, str]] = None,
) -> Optional[str]:
    """Resolve a video reference to a staged static path.

    Resolution order:
      1. Per-section logical alias map, used to translate names like
         `veo/ocean_sunset.mp4` to the actual staged clip for another visual.
      2. Exact staged path as written in the spec.
      3. Compatibility fallback candidates under remotion/public.
    """
    normalized = raw_value.replace('\\', '/').lstrip('/')
    if not normalized:
        return None

    if reference_aliases:
        for key in _normalize_reference_stems(normalized):
            resolved = reference_aliases.get(key)
            if resolved and os.path.isfile(os.path.join(remotion_public, resolved)):
                return resolved

    exact = _resolve_media_static_path(remotion_public, normalized)
    if exact is not None:
        return exact

    return _existing_static_path(
        remotion_public,
        _candidate_video_static_paths(normalized),
    )


def _candidate_video_static_paths(raw_value: str) -> List[str]:
    """Build likely staged staticFile() paths for a structured video reference."""
    normalized = raw_value.replace('\\', '/').lstrip('/')
    if not normalized:
        return []

    candidates: List[str] = []

    def _add(candidate: str) -> None:
        if candidate and candidate not in candidates:
            candidates.append(candidate)

    if Path(normalized).suffix.lower() in VIDEO_EXTENSIONS:
        _add(normalized)
        basename = normalized.split('/')[-1]
        if not normalized.startswith('veo/'):
            _add(f'veo/{basename}')
            _add(basename)

    for stem in _normalize_reference_stems(normalized):
        stem_basename = stem.split('/')[-1]
        for ext in VIDEO_EXTENSION_PRIORITY:
            if stem.endswith(ext):
                _add(stem)
                _add(stem_basename)
                continue
            _add(f'veo/{stem_basename}{ext}')
            _add(f'{stem_basename}{ext}')

    return candidates


def _resolve_structured_video_static_path(
    spec_content: str,
    remotion_public: str,
    reference_aliases: Optional[Dict[str, str]] = None,
) -> Optional[str]:
    """Resolve a staged video path from structured spec fields like outputFile / clip_id."""
    if not remotion_public:
        return None

    for _, raw_value in STRUCTURED_VIDEO_FIELD_RE.findall(spec_content):
        resolved = _resolve_video_reference_static_path(
            remotion_public,
            raw_value,
            reference_aliases,
        )
        if resolved is not None:
            return resolved

    return None


def _resolve_generated_spec_basename_video(
    spec_base: str,
    remotion_public: str,
) -> Optional[str]:
    """Resolve the staged clip generated for a spec basename."""
    if not remotion_public:
        return None

    return _existing_static_path(
        remotion_public,
        [f'veo/{spec_base}{ext}' for ext in VIDEO_EXTENSION_PRIORITY],
    )


def _iter_video_reference_values(spec_content: str) -> List[str]:
    """Collect logical video references declared inside a spec."""
    values: List[str] = []

    def _add(raw_value: str) -> None:
        normalized = raw_value.replace('\\', '/').lstrip('/')
        if normalized and normalized not in values:
            values.append(normalized)

    for _, raw_value in STRUCTURED_VIDEO_FIELD_RE.findall(spec_content):
        _add(raw_value)
    for _, raw_value in GENERIC_VIDEO_REF_RE.findall(spec_content):
        _add(raw_value)
    for rel_path in STATIC_FILE_RE.findall(spec_content):
        if Path(rel_path).suffix.lower() in VIDEO_EXTENSIONS:
            _add(rel_path)
    data_points = _extract_data_points_json(spec_content)
    if data_points is not None:
        for raw_value in _iter_data_point_media_values(data_points):
            _add(raw_value)

    return values


def _build_section_video_reference_aliases(
    visual_ids: List[str],
    spec_dir: str,
    section_id: str,
    remotion_public: str,
) -> Dict[str, str]:
    """Map logical spec video names to the actual staged clips for this section."""
    aliases: Dict[str, str] = {}
    if not spec_dir or not remotion_public:
        return aliases

    for visual_id in visual_ids:
        spec_base = component_base_name(visual_id, section_id)
        spec_path = os.path.join(spec_dir, f'{spec_base}.md')
        if not os.path.isfile(spec_path):
            continue

        spec_content = _read_text_if_exists(spec_path)
        if not spec_content:
            continue

        refs = _iter_video_reference_values(spec_content)
        staged_target = _resolve_generated_spec_basename_video(spec_base, remotion_public)
        resolved_refs = [
            (ref, _resolve_media_static_path(remotion_public, ref))
            for ref in refs
        ]
        distinct_resolved_targets = {
            resolved for _, resolved in resolved_refs if resolved is not None
        }

        if len(distinct_resolved_targets) > 1:
            for ref, resolved in resolved_refs:
                if resolved is None:
                    continue
                for key in _normalize_reference_stems(ref):
                    aliases.setdefault(key, resolved)
            continue

        direct_target = next(
            (resolved for _, resolved in resolved_refs if resolved is not None),
            None,
        )
        canonical_target = staged_target or direct_target
        if canonical_target is None:
            continue

        for ref in refs:
            for key in _normalize_reference_stems(ref):
                aliases[key] = canonical_target

    return aliases


def _extract_visual_media_aliases(
    spec_content: str,
    remotion_public: str,
    inherited_default: Optional[str],
    spec_base: str,
    reference_aliases: Optional[Dict[str, str]] = None,
) -> tuple[Dict[str, str], Optional[str], bool]:
    """Extract named Veo asset aliases from a spec file."""
    explicit_sources: List[str] = []
    aliases: Dict[str, str] = {}
    explicit = False

    for key, rel_path in VISUAL_MEDIA_KEY_RE.findall(spec_content):
        resolved = _resolve_video_reference_static_path(
            remotion_public,
            rel_path,
            reference_aliases,
        )
        if resolved is None:
            continue
        explicit = True
        if resolved not in explicit_sources:
            explicit_sources.append(resolved)
        alias_name = MEDIA_ALIAS_KEY_MAP.get(key.lower())
        if alias_name:
            aliases[alias_name] = resolved

    data_points = _extract_data_points_json(spec_content)
    if data_points is not None:
        structured_aliases = _extract_data_point_media_aliases(
            data_points,
            remotion_public,
            reference_aliases,
        )
        for alias_name, resolved in structured_aliases.items():
            explicit = True
            if resolved not in explicit_sources:
                explicit_sources.append(resolved)
            aliases.setdefault(alias_name, resolved)

    structured_default = _resolve_structured_video_static_path(
        spec_content,
        remotion_public,
        reference_aliases,
    )
    if structured_default is not None:
        explicit = True
        if structured_default not in explicit_sources:
            explicit_sources.append(structured_default)
        aliases.setdefault('defaultSrc', structured_default)

    for _, raw_value in GENERIC_VIDEO_REF_RE.findall(spec_content):
        resolved = _resolve_video_reference_static_path(
            remotion_public,
            raw_value,
            reference_aliases,
        )
        if resolved is None:
            continue
        explicit = True
        if resolved not in explicit_sources:
            explicit_sources.append(resolved)

    for rel_path in STATIC_FILE_RE.findall(spec_content):
        if Path(rel_path).suffix.lower() not in VIDEO_EXTENSIONS:
            continue
        resolved = _resolve_video_reference_static_path(
            remotion_public,
            rel_path,
            reference_aliases,
        )
        if resolved is None:
            continue
        explicit = True
        if resolved not in explicit_sources:
            explicit_sources.append(resolved)

    if not explicit_sources:
        generated_default = _resolve_generated_spec_basename_video(
            spec_base,
            remotion_public,
        )
        if generated_default is not None:
            explicit_sources.append(generated_default)
            aliases.setdefault('defaultSrc', generated_default)

    primary = aliases.get('defaultSrc')
    if primary is None and explicit_sources:
        primary = explicit_sources[0]
        aliases['defaultSrc'] = primary
    if primary is None:
        primary = inherited_default

    if primary is not None:
        aliases.setdefault('defaultSrc', primary)
        aliases.setdefault('backgroundSrc', primary)
        aliases.setdefault('outputSrc', primary)
        aliases.setdefault('baseSrc', primary)

    if len(explicit_sources) >= 2:
        aliases.setdefault('leftSrc', explicit_sources[0])
        aliases.setdefault('rightSrc', explicit_sources[1])
        aliases.setdefault('baseSrc', explicit_sources[0])
        aliases.setdefault('revealSrc', explicit_sources[1])

    return aliases, primary, explicit


def build_visual_contract_manifest(
    sections: List[Dict[str, Any]],
    project_dir: str,
    remotion_public: str,
) -> Dict[str, Any]:
    """Build a persisted structured visual contract manifest for Stage 8+ consumers."""
    manifest_sections: List[Dict[str, Any]] = []

    for section in sections:
        visual_ids = resolve_section_visual_ids(section, project_dir, remotion_public)
        if not visual_ids:
            continue

        spec_dir = section.get('specDir') or section['id']
        if not os.path.isabs(spec_dir):
            spec_dir = os.path.join(
                project_dir,
                'specs',
                str(spec_dir).replace('\\', '/').replace('specs/', '').strip('/'),
            )

        media_manifest = build_visual_media_manifest(
            section,
            project_dir,
            remotion_public,
        )
        overlay_manifest = build_visual_overlay_manifest(section, project_dir)
        visuals: List[Dict[str, Any]] = []
        for visual_id in visual_ids:
            spec_base = component_base_name(visual_id, section['id'])
            spec_path = os.path.join(spec_dir, f'{spec_base}.md')
            spec_content = _read_text_if_exists(spec_path)
            data_points = _extract_data_points_json(spec_content) if spec_content else None
            visuals.append({
                'id': visual_id,
                'specBaseName': spec_base,
                'specPath': os.path.relpath(spec_path, project_dir).replace('\\', '/') if spec_content else None,
                'dataPoints': data_points,
                'mediaAliases': media_manifest.get(visual_id, {}),
                'overlayConfig': overlay_manifest.get(visual_id),
            })

        manifest_sections.append({
            'id': section['id'],
            'visuals': visuals,
        })

    return {
        'version': 1,
        'updatedAt': datetime.now(timezone.utc).isoformat(),
        'sections': manifest_sections,
    }


def write_visual_contract_manifest(
    sections: List[Dict[str, Any]],
    project_dir: str,
    remotion_public: str,
) -> str:
    """Persist the generated visual contract manifest beside composition outputs."""
    manifest = build_visual_contract_manifest(sections, project_dir, remotion_public)
    manifest_path = os.path.join(project_dir, 'outputs', 'compositions', 'visual-manifest.json')
    os.makedirs(os.path.dirname(manifest_path), exist_ok=True)
    with open(manifest_path, 'w', encoding='utf-8') as f:
        json.dump(manifest, f, indent=2)
    return manifest_path


def build_section_visual_contract_map(
    section: Dict[str, Any],
    project_dir: str,
    remotion_public: str,
) -> Dict[str, Dict[str, Any]]:
    """Return a section-local visual contract map keyed by visual id."""
    manifest = build_visual_contract_manifest([section], project_dir, remotion_public)
    section_entry = next(iter(manifest.get('sections', [])), None)
    if not section_entry:
        return {}

    contracts: Dict[str, Dict[str, Any]] = {}
    for visual in section_entry.get('visuals', []):
        contracts[visual['id']] = {
            'specBaseName': visual.get('specBaseName'),
            'dataPoints': visual.get('dataPoints'),
            'overlayConfig': visual.get('overlayConfig'),
        }
    return contracts


def build_visual_media_manifest(
    section: Dict[str, Any],
    project_dir: str,
    remotion_public: str,
    fallback_video_src: Optional[str] = None,
) -> Dict[str, Dict[str, str]]:
    """Build per-visual media aliases for the section wrapper."""
    visual_ids = resolve_section_visual_ids(section, project_dir, remotion_public)
    if not visual_ids or not project_dir or not remotion_public:
        return {}

    spec_dir = section.get('specDir') or section['id']
    if not os.path.isabs(spec_dir):
        spec_dir = os.path.join(project_dir, 'specs', str(spec_dir).replace('\\', '/').replace('specs/', '').strip('/'))

    manifest: Dict[str, Dict[str, str]] = {}
    inherited_default: Optional[str] = None
    saw_explicit_source = False
    reference_aliases = _build_section_video_reference_aliases(
        visual_ids,
        spec_dir,
        section['id'],
        remotion_public,
    )

    for visual_id in visual_ids:
        spec_base = component_base_name(visual_id, section['id'])
        spec_path = os.path.join(spec_dir, f'{spec_base}.md')
        aliases: Dict[str, str] = {}

        if os.path.isfile(spec_path):
            aliases, next_default, explicit = _extract_visual_media_aliases(
                _read_text_if_exists(spec_path),
                remotion_public,
                inherited_default,
                spec_base,
                reference_aliases,
            )
            if explicit:
                saw_explicit_source = True
            if next_default is not None:
                inherited_default = next_default
        elif inherited_default is not None:
            aliases = {
                'defaultSrc': inherited_default,
                'backgroundSrc': inherited_default,
                'outputSrc': inherited_default,
                'baseSrc': inherited_default,
            }

        if not aliases and not saw_explicit_source and fallback_video_src is not None:
            aliases = {
                'defaultSrc': fallback_video_src,
                'backgroundSrc': fallback_video_src,
                'outputSrc': fallback_video_src,
                'baseSrc': fallback_video_src,
            }

        if aliases:
            manifest[visual_id] = aliases

    return manifest


def _extract_narration_text(spec_content: str) -> Optional[str]:
    """Extract narration text for generic lower-third overlays."""
    narration_match = NARRATION_SYNC_RE.search(spec_content)
    if narration_match:
        return narration_match.group(1).strip()

    narration_json_match = NARRATION_JSON_RE.search(spec_content)
    if narration_json_match:
        return narration_json_match.group(1).strip()

    return None


def _extract_visual_overlay_config(spec_content: str) -> Optional[Dict[str, Any]]:
    """Build a generic overlay config for media-plus-overlay specs.

    This is intentionally data-driven and only emits generic overlays that can
    be rendered consistently across projects without requiring a bespoke
    generated Remotion component per spec.
    """
    normalized = spec_content.lower()
    config: Dict[str, Any] = {}

    if (
        'gradientoverlay' in normalized
        or 'color grade overlay' in normalized
        or 'linear gradient' in normalized
    ):
        config['gradientOverlay'] = 'bottom'

    if (
        'lightbloomoverlay' in normalized
        or 'light bloom overlay' in normalized
        or 'radial gradient at top-right' in normalized
    ):
        config['lightBloom'] = True

    if 'lower-third' in normalized or 'lowerthirdbadge' in normalized:
        narration_text = _extract_narration_text(spec_content)
        if narration_text:
            config['lowerThirdText'] = narration_text

    return config or None


def build_visual_overlay_manifest(
    section: Dict[str, Any],
    project_dir: str,
) -> Dict[str, Dict[str, Any]]:
    """Build generic overlay configs for media-based visuals.

    These overlays are used when a spec describes composited media but there is
    no dedicated Remotion component for that visual.
    """
    visual_ids = resolve_section_visual_ids(section, project_dir)
    if not visual_ids or not project_dir:
        return {}

    spec_dir = section.get('specDir') or section['id']
    if not os.path.isabs(spec_dir):
        spec_dir = os.path.join(project_dir, 'specs', str(spec_dir).replace('\\', '/').replace('specs/', '').strip('/'))

    manifest: Dict[str, Dict[str, Any]] = {}
    for visual_id in visual_ids:
        spec_base = component_base_name(visual_id, section['id'])
        spec_path = os.path.join(spec_dir, f'{spec_base}.md')
        if not os.path.isfile(spec_path):
            continue

        overlay_config = _extract_visual_overlay_config(_read_text_if_exists(spec_path))
        if overlay_config:
            manifest[visual_id] = overlay_config

    return manifest


def resolve_component_intrinsic_duration_frames(
    comp_id: str,
    section_id: str,
    remotion_src: str,
) -> Optional[int]:
    """Best-effort duration discovery from generated component constants.ts."""
    if not remotion_src:
        return None

    _, import_path = resolve_comp_import(comp_id, section_id, remotion_src)
    constants_candidates = [
        os.path.join(remotion_src, import_path, 'constants.ts'),
        os.path.join(remotion_src, f'{import_path}.tsx'),
    ]

    duration_re = re.compile(r'totalDuration\s*[:=]\s*(\d+)', re.IGNORECASE)

    for candidate in constants_candidates:
        content = _read_text_if_exists(candidate)
        if not content:
            continue
        match = duration_re.search(content)
        if match:
            try:
                duration = int(match.group(1))
            except ValueError:
                continue
            if duration > 0:
                return duration

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
    remotion_public: str,
    project_dir: str,
) -> Optional[str]:
    """Generate a deterministic wrapper for Stage 8-generated section timelines.

    Claude can generate component files and constants nondeterministically, but
    the final section wrapper must remain deterministic. When a section has a
    generated composition graph and constants.ts exists, we render the active
    visual directly from VISUAL_SEQUENCE using exact filesystem-resolved imports.
    """
    section_id = section['id']
    if not remotion_src:
        return None

    constants_path = os.path.join(remotion_src, section_id, 'constants.ts')
    if not os.path.isfile(constants_path):
        return None

    pascal_name = to_pascal_case(section_id)
    component_name = f'{pascal_name}Section'
    duration_seconds = section.get('durationSeconds', 0)
    compositions: List[Dict[str, Any]] = section.get('compositions', [])
    visual_media_manifest = build_visual_media_manifest(
        section,
        project_dir,
        remotion_public,
        direct_video_src if needs_direct_video else None,
    )
    visual_overlay_manifest = build_visual_overlay_manifest(
        section,
        project_dir,
    )
    visual_contract_map = build_section_visual_contract_map(
        section,
        project_dir,
        remotion_public,
    )

    resolved_components: List[tuple[str, str, str]] = []
    component_durations: Dict[str, int] = {}
    for comp in compositions:
        comp_id = comp if isinstance(comp, str) else comp.get('id', '')
        if not comp_id or comp_id.startswith('veo:'):
            continue
        comp_pascal, import_path = resolve_comp_import(comp_id, section_id, remotion_src)
        resolved_components.append((comp_id, comp_pascal, import_path))
        intrinsic_duration = resolve_component_intrinsic_duration_frames(
            comp_id,
            section_id,
            remotion_src,
        )
        if intrinsic_duration is not None:
            component_durations[comp_id] = intrinsic_duration

    remotion_imports = ['Sequence', 'useCurrentFrame']
    if needs_direct_audio:
        remotion_imports.append('Audio')
    has_visual_video = bool(visual_media_manifest) or needs_direct_video
    if has_visual_video:
        remotion_imports.append('OffthreadVideo')
    if needs_direct_audio or has_visual_video:
        remotion_imports.append('staticFile')

    lines: List[str] = []
    lines.append('import React from "react";')
    lines.append(f'import {{ {", ".join(remotion_imports)} }} from "remotion";')
    lines.append('import { VISUAL_SEQUENCE } from "./constants";')
    lines.append('import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";')
    if visual_overlay_manifest:
        lines.append('import { GeneratedMediaVisual } from "../_shared/GeneratedMediaVisual";')

    for _, comp_pascal, import_path in resolved_components:
        lines.append(f'import {{ {comp_pascal} }} from "../{import_path}";')

    lines.append('')
    lines.append('const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {')
    for comp_id, comp_pascal, _ in resolved_components:
        lines.append(f'  "{comp_id}": {comp_pascal},')
    lines.append('};')
    lines.append('')
    lines.append('const VISUAL_DURATIONS: Record<string, number> = {')
    for comp_id, duration in component_durations.items():
        lines.append(f'  "{comp_id}": {duration},')
    lines.append('};')
    lines.append('')
    lines.append('const VISUAL_MEDIA: Record<string, Record<string, string>> = {')
    for visual_id, aliases in visual_media_manifest.items():
        alias_parts = ', '.join(
            f'{alias_name}: "{alias_value}"'
            for alias_name, alias_value in aliases.items()
        )
        lines.append(f'  "{visual_id}": {{ {alias_parts} }},')
    lines.append('};')
    lines.append('')
    lines.append('const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {')
    for visual_id, config in visual_overlay_manifest.items():
        overlay_parts: List[str] = []
        for key, value in config.items():
            if isinstance(value, bool):
                serialized = 'true' if value else 'false'
            else:
                serialized = json.dumps(str(value))
            overlay_parts.append(f'{key}: {serialized}')
        lines.append(f'  "{visual_id}": {{ {", ".join(overlay_parts)} }},')
    lines.append('};')
    lines.append('')
    lines.append('const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {')
    for visual_id, contract in visual_contract_map.items():
        lines.append(f'  "{visual_id}": {json.dumps(contract, ensure_ascii=False)},')
    lines.append('};')
    lines.append('')
    lines.append(f'export const {component_name}: React.FC = () => {{')
    lines.append(f'  const fps = {fps};')
    lines.append(f'  const durationSeconds = {duration_seconds};')
    lines.append('  const frame = useCurrentFrame();')
    lines.append('  const activeVisuals = VISUAL_SEQUENCE.filter((visual) => frame >= visual.start && frame < visual.end);')
    lines.append('')
    lines.append('  return (')
    lines.append('    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>')
    if needs_direct_audio and direct_audio_src is not None:
        lines.append(f'      <Audio src={{staticFile("{direct_audio_src}")}} />')
    if needs_direct_video and direct_video_src is not None:
        lines.append(f'      {{activeVisuals.length === 0 ? <OffthreadVideo src={{staticFile("{direct_video_src}")}} style={{{{ width: "100%", height: "100%" }}}} /> : null}}')
    lines.append('      {activeVisuals.map((visual) => {')
    lines.append('        const VisualComponent = COMPONENT_MAP[visual.id] ?? null;')
    lines.append('        const visualDuration = Math.max(1, visual.end - visual.start);')
    lines.append('        const intrinsicDurationInFrames = VISUAL_DURATIONS[visual.id] ?? visualDuration;')
    lines.append('        const visualMedia = VISUAL_MEDIA[visual.id] ?? null;')
    lines.append('        const visualOverlayConfig = VISUAL_OVERLAYS[visual.id] ?? null;')
    lines.append('        const visualContract = VISUAL_CONTRACTS[visual.id] ?? null;')
    lines.append('')
    lines.append('        return (')
    lines.append('          <Sequence key={visual.id} from={visual.start} durationInFrames={visualDuration}>')
    lines.append('            {VisualComponent ? (')
    lines.append('              <SlotScaledSequence intrinsicDurationInFrames={intrinsicDurationInFrames}>')
    lines.append('                <VisualContractProvider contract={visualContract}>')
    lines.append('                  <VisualMediaProvider media={visualMedia}>')
    lines.append('                    <VisualComponent />')
    lines.append('                  </VisualMediaProvider>')
    lines.append('                </VisualContractProvider>')
    lines.append('              </SlotScaledSequence>')
    if visual_media_manifest:
        lines.append('            ) : visualMedia?.defaultSrc ? (')
        lines.append('              <VisualContractProvider contract={visualContract}>')
        lines.append('                <VisualMediaProvider media={visualMedia}>')
        if visual_overlay_manifest:
            lines.append('                {visualOverlayConfig || visualMedia?.leftSrc || visualMedia?.rightSrc ? (')
            lines.append('                  <GeneratedMediaVisual config={visualOverlayConfig} />')
            lines.append('                ) : (')
            lines.append('                  <OffthreadVideo src={staticFile(visualMedia.defaultSrc)} style={{ width: "100%", height: "100%" }} />')
            lines.append('                )}')
        else:
            lines.append('                <OffthreadVideo src={staticFile(visualMedia.defaultSrc)} style={{ width: "100%", height: "100%" }} />')
        lines.append('                </VisualMediaProvider>')
        lines.append('              </VisualContractProvider>')
        lines.append('            ) : null}')
    else:
        lines.append('            ) : null}')
    lines.append('          </Sequence>')
    lines.append('        );')
    lines.append('      })}')
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
        remotion_public,
        project_dir,
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
    lines.append(f'    <Sequence from={{0}} durationInFrames={{Math.max(1, Math.ceil(durationSeconds * fps))}}>')

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
    default_width: int = 1920,
    default_height: int = 1080,
    project_dir: str = '',
) -> str:
    """Generate the Root.tsx content that registers all section compositions
    and individual component compositions for preview."""
    lines: List[str] = []
    remotion_src = os.path.join(remotion_dir, 'src', 'remotion') if remotion_dir else ''
    remotion_public = os.path.join(remotion_dir, 'public') if remotion_dir else ''
    preview_media_records: List[tuple[str, str, Dict[str, str]]] = []
    preview_contract_records: List[tuple[str, str, Dict[str, Any]]] = []
    preview_wrapper_names: Dict[str, str] = {}
    section_contract_lookup: Dict[str, Dict[str, Dict[str, Any]]] = {}

    if project_dir and remotion_public:
        visual_contract_manifest = build_visual_contract_manifest(
            sections,
            project_dir,
            remotion_public,
        )
        for section_entry in visual_contract_manifest.get('sections', []):
            section_contract_lookup[section_entry['id']] = {
                visual['id']: {
                    'specBaseName': visual.get('specBaseName'),
                    'dataPoints': visual.get('dataPoints'),
                    'overlayConfig': visual.get('overlayConfig'),
                }
                for visual in section_entry.get('visuals', [])
            }

    for section in sections:
        if not project_dir or not remotion_public:
            continue

        fallback_video_src = resolve_direct_video_src(section['id'], remotion_public)
        visual_media_manifest = build_visual_media_manifest(
            section,
            project_dir,
            remotion_public,
            fallback_video_src=fallback_video_src,
        )

        compositions = section.get('compositions', [])
        for comp in compositions:
            comp_id = comp if isinstance(comp, str) else comp.get('id', '')
            if not comp_id:
                continue
            media = visual_media_manifest.get(comp_id)
            contract = section_contract_lookup.get(section['id'], {}).get(comp_id)
            if not media:
                if not contract:
                    continue
            comp_pascal, _ = resolve_comp_import(comp_id, section['id'], remotion_src)
            preview_wrapper_names[comp_pascal] = f'{comp_pascal}Preview'
            if media:
                preview_media_records.append((section['id'], comp_id, media))
            if contract:
                preview_contract_records.append((section['id'], comp_id, contract))

    lines.append('import React from "react";')
    lines.append('import { Composition } from "remotion";')
    if preview_media_records or preview_contract_records:
        imports = ['VisualMediaProvider']
        if preview_contract_records:
            imports.append('VisualContractProvider')
        lines.append(f'import {{ {", ".join(imports)} }} from "./_shared/visual-runtime";')
    lines.append('')

    # Import all section components (always from wrapper directory)
    for section in sections:
        section_id = section['id']
        pascal_name = to_pascal_case(section_id)
        component_name = f'{pascal_name}Section'
        lines.append(f'import {{ {component_name} }} from "./{section_id}";')

    # Import individual components for preview compositions
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
    if preview_media_records or preview_contract_records:
        lines.append('const PREVIEW_VISUAL_MEDIA: Record<string, Record<string, string>> = {')
        for section_id, comp_id, aliases in preview_media_records:
            alias_parts = ', '.join(
                f'{alias_name}: "{alias_value}"'
                for alias_name, alias_value in aliases.items()
            )
            lines.append(f'  "{section_id}:{comp_id}": {{ {alias_parts} }},')
        lines.append('};')
        lines.append('')
        lines.append('const PREVIEW_VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {')
        for section_id, comp_id, contract in preview_contract_records:
            lines.append(f'  "{section_id}:{comp_id}": {json.dumps(contract, ensure_ascii=False)},')
        lines.append('};')
        lines.append('')
        generated_preview_wrappers: set = set()
        for section in sections:
            section_id = section['id']
            compositions = section.get('compositions', [])
            for comp in compositions:
                comp_id = comp if isinstance(comp, str) else comp.get('id', '')
                if not comp_id:
                    continue
                comp_pascal, _ = resolve_comp_import(comp_id, section_id, remotion_src)
                preview_wrapper_name = preview_wrapper_names.get(comp_pascal)
                if not preview_wrapper_name or preview_wrapper_name in generated_preview_wrappers:
                    continue
                lines.append(f'const {preview_wrapper_name}: React.FC = () => (')
                lines.append(f'  <VisualContractProvider contract={{PREVIEW_VISUAL_CONTRACTS["{section_id}:{comp_id}"] ?? null}}>')
                lines.append(f'    <VisualMediaProvider media={{PREVIEW_VISUAL_MEDIA["{section_id}:{comp_id}"] ?? null}}>')
                lines.append(f'      <{comp_pascal} />')
                lines.append('    </VisualMediaProvider>')
                lines.append('  </VisualContractProvider>')
                lines.append(');')
                generated_preview_wrappers.add(preview_wrapper_name)
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
        duration_frames = max(1, math.ceil(duration_seconds * fps))
        width = section.get('width', default_width)
        height = section.get('height', default_height)

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
        width = section.get('width', default_width)
        height = section.get('height', default_height)
        for comp in compositions:
            comp_id = comp if isinstance(comp, str) else comp.get('id', '')
            if comp_id:
                comp_pascal, _ = resolve_comp_import(comp_id, section_id, remotion_src)
                if comp_pascal in registered:
                    continue
                preview_component = preview_wrapper_names.get(comp_pascal, comp_pascal)
                # Use hyphenated comp_pascal as the Remotion composition ID
                # to ensure uniqueness across sections
                remotion_id = re.sub(r'([a-z0-9])([A-Z])', r'\1-\2', comp_pascal).lower()
                lines.append(f'      <Composition')
                lines.append(f'        id="{remotion_id}"')
                lines.append(f'        component={{{preview_component}}}')
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
    default_width: int = 1920,
    default_height: int = 1080,
    project_dir: str = '',
) -> None:
    """Update or create Root.tsx to register all section compositions."""
    root_path = os.path.join(remotion_dir, 'src', 'remotion', 'Root.tsx')
    root_dir = os.path.dirname(root_path)
    os.makedirs(root_dir, exist_ok=True)

    # Always regenerate Root.tsx from scratch to ensure all section and
    # individual component compositions are correctly registered.
    new_content = generate_root_tsx(
        sections,
        fps,
        remotion_dir,
        default_width=default_width,
        default_height=default_height,
        project_dir=project_dir,
    )

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
        duration_frames = max(1, math.ceil(duration_seconds * fps))
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

    output_resolution = project_data.get('outputResolution') or {}
    default_width = int(output_resolution.get('width', 1920))
    default_height = int(output_resolution.get('height', 1080))

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
    update_root_tsx(
        sections,
        fps,
        remotion_dir,
        default_width=default_width,
        default_height=default_height,
        project_dir=project_dir,
    )

    remotion_public = os.path.join(remotion_dir, 'public')
    write_visual_contract_manifest(
        sections,
        project_dir,
        remotion_public,
    )

    sys.exit(0)


if __name__ == '__main__':
    main()
