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
    resolved = _resolve_existing_comp_import(comp_id, section_id, remotion_src)
    if resolved is not None:
        return resolved

    comp_pascal = to_pascal_case(comp_id)
    section_pascal = to_pascal_case(section_id)
    if comp_pascal and comp_pascal[0].isdigit():
        comp_pascal = section_pascal + comp_pascal
    return (comp_pascal, comp_id)


def _normalize_component_lookup_key(value: str, section_id: str) -> str:
    """Normalize component names for semantic matching across numbering drift."""
    normalized = value.strip()
    section_pascal = to_pascal_case(section_id)
    if section_pascal and normalized.startswith(section_pascal):
        normalized = normalized[len(section_pascal):]
    normalized = component_base_name(normalized, section_id)
    normalized = re.sub(r'^[0-9]+', '', normalized)
    return re.sub(r'[^a-z0-9]+', '', normalized.lower())


def _normalize_component_tokens(value: str) -> List[str]:
    """Normalize a component identifier into fuzzy-match tokens."""
    normalized = re.sub(r'([a-z0-9])([A-Z])', r'\1 \2', value)
    normalized = normalized.replace('_', ' ').replace('-', ' ')
    normalized = re.sub(r'([0-9]+)', ' ', normalized)
    tokens: List[str] = []
    for raw_token in normalized.lower().split():
        token = raw_token.strip()
        if not token:
            continue
        if token.endswith('ing') and len(token) > 5:
            token = token[:-3]
        elif token.endswith('ed') and len(token) > 4:
            token = token[:-2]
        elif token.endswith('s') and len(token) > 4:
            token = token[:-1]
        tokens.append(token)
    return tokens


def _leading_component_index(value: str) -> Optional[str]:
    """Return the leading numeric prefix from a component identifier, if any."""
    match = re.match(r'^\D*?(\d+)', value.strip())
    return match.group(1) if match else None


def _resolve_component_export_name(
    import_path: str,
    remotion_src: str,
    fallback_name: str,
) -> str:
    """Read the named export for an import path when the filesystem name is not a safe identifier."""
    candidate_paths = [
        os.path.join(remotion_src, import_path, 'index.ts'),
        os.path.join(remotion_src, import_path, 'index.tsx'),
        os.path.join(remotion_src, f'{import_path}.ts'),
        os.path.join(remotion_src, f'{import_path}.tsx'),
    ]
    export_patterns = (
        re.compile(r'export\s*\{\s*([A-Za-z_][A-Za-z0-9_]*)'),
        re.compile(r'export\s+const\s+([A-Za-z_][A-Za-z0-9_]*)'),
        re.compile(r'export\s+function\s+([A-Za-z_][A-Za-z0-9_]*)'),
        re.compile(r'export\s+class\s+([A-Za-z_][A-Za-z0-9_]*)'),
    )

    for candidate_path in candidate_paths:
        if not os.path.isfile(candidate_path):
            continue
        try:
            source = _read_text_if_exists(candidate_path)
        except OSError:
            continue
        if not source:
            continue
        for pattern in export_patterns:
            match = pattern.search(source)
            if match:
                return match.group(1)

    return fallback_name


def _iter_component_import_candidates(remotion_src: str) -> List[tuple[str, str]]:
    """List importable component targets under remotion/src/remotion."""
    if not remotion_src or not os.path.isdir(remotion_src):
        return []

    candidates: List[tuple[str, str]] = []
    for entry in sorted(os.listdir(remotion_src)):
        if entry.startswith('.'):
            continue
        abs_path = os.path.join(remotion_src, entry)
        if os.path.isdir(abs_path):
            candidates.append((entry, entry))
            continue
        if entry.endswith('.tsx'):
            stem = os.path.splitext(entry)[0]
            candidates.append((stem, stem))
    return candidates


def _resolve_existing_comp_import(
    comp_id: str,
    section_id: str,
    remotion_src: str,
    allow_fuzzy: bool = True,
) -> Optional[tuple[str, str]]:
    """Resolve an actual import target when a generated component exists on disk."""
    comp_pascal = to_pascal_case(comp_id)
    section_pascal = to_pascal_case(section_id)
    if comp_pascal and comp_pascal[0].isdigit():
        comp_pascal = section_pascal + comp_pascal
    fallback_export_name = resolve_logical_component_name(comp_id, section_id)

    if not remotion_src:
        return None

    pascal_dir = os.path.join(remotion_src, comp_pascal)
    if os.path.isdir(pascal_dir):
        return (
            _resolve_component_export_name(comp_pascal, remotion_src, fallback_export_name),
            comp_pascal,
        )

    parts = re.split(r'[_\-]', comp_id)
    kebab_name = parts[0] + '-' + ''.join(p.capitalize() for p in parts[1:] if p) if len(parts) > 1 else comp_id
    kebab_dir = os.path.join(remotion_src, kebab_name)
    if os.path.isdir(kebab_dir):
        return (
            _resolve_component_export_name(kebab_name, remotion_src, fallback_export_name),
            kebab_name,
        )

    flat_file = os.path.join(remotion_src, f'{comp_id}.tsx')
    if os.path.isfile(flat_file):
        return (
            _resolve_component_export_name(comp_id, remotion_src, fallback_export_name),
            comp_id,
        )

    target_key = _normalize_component_lookup_key(comp_id, section_id)
    if not target_key:
        return None

    matches = [
        candidate
        for candidate in _iter_component_import_candidates(remotion_src)
        if _normalize_component_lookup_key(candidate[0], section_id) == target_key
    ]
    if matches:
        section_matches = [
            candidate
            for candidate in matches
            if candidate[0].startswith(section_pascal)
        ]
        if len(section_matches) == 1:
            _, import_path = section_matches[0]
            return (
                _resolve_component_export_name(import_path, remotion_src, fallback_export_name),
                import_path,
            )
        if len(matches) == 1:
            _, import_path = matches[0]
            return (
                _resolve_component_export_name(import_path, remotion_src, fallback_export_name),
                import_path,
            )

    if not allow_fuzzy:
        return None

    target_tokens = _normalize_component_tokens(comp_id)
    if not target_tokens:
        return None

    target_index = _leading_component_index(comp_id)
    scored_matches: List[tuple[float, tuple[str, str]]] = []
    for candidate in _iter_component_import_candidates(remotion_src):
        candidate_name = candidate[0]
        candidate_tokens = _normalize_component_tokens(candidate_name)
        if not candidate_tokens:
            continue

        overlap = sum(1 for token in target_tokens if token in candidate_tokens) / len(target_tokens)
        if overlap < 0.6:
            continue

        score = overlap
        if candidate_name.startswith(section_pascal):
            score += 0.1
        if target_index and _leading_component_index(candidate_name) == target_index:
            score += 0.15

        scored_matches.append((score, candidate))

    if not scored_matches:
        return None

    scored_matches.sort(key=lambda item: item[0], reverse=True)
    best_score, best_candidate = scored_matches[0]
    if best_score < 0.8:
        return None
    if len(scored_matches) > 1 and scored_matches[1][0] >= best_score - 0.05:
        return None
    _, (_, import_path) = scored_matches[0]
    return (
        _resolve_component_export_name(import_path, remotion_src, fallback_export_name),
        import_path,
    )

    return None


def resolve_preview_composition_id(comp_id: str, section_id: str) -> str:
    """Mirror the TS preview composition id for logical visual ids."""
    comp_pascal = to_pascal_case(comp_id)
    if comp_pascal and comp_pascal[0].isdigit():
        comp_pascal = f'{to_pascal_case(section_id)}{comp_pascal}'
    return re.sub(r'([a-z0-9])([A-Z])', r'\1-\2', comp_pascal).lower()


def resolve_logical_component_name(comp_id: str, section_id: str) -> str:
    """Return a safe PascalCase identifier for a logical visual id."""
    comp_pascal = to_pascal_case(comp_id)
    if comp_pascal and comp_pascal[0].isdigit():
        comp_pascal = f'{to_pascal_case(section_id)}{comp_pascal}'
    return comp_pascal


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
    r'(?:^|\n)##\s*Data Points(?:\s+JSON)?\s*(?:\r?\n)+```json\s*([\s\S]+?)\s*```',
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
    'clipid': 'defaultSrc',
    'leftclip': 'leftSrc',
    'leftclipid': 'leftSrc',
    'leftsrc': 'leftSrc',
    'rightclip': 'rightSrc',
    'rightclipid': 'rightSrc',
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
    'clipsource',
    'clip',
    'clipid',
    'leftclipid',
    'rightclipid',
    'leftsrc',
    'rightsrc',
    'backgroundclip',
    'backgroundsrc',
    'baseclip',
    'basesrc',
    'revealclip',
    'revealsrc',
    'videosource',
    'videosrc',
    'video',
    'outputsrc',
    'outputfile',
    'filename',
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
MEDIA_SEARCH_STOPWORDS = {
    'the',
    'and',
    'for',
    'with',
    'from',
    'into',
    'through',
    'over',
    'under',
    'this',
    'that',
    'these',
    'those',
    'your',
    'their',
    'frame',
    'frames',
    'section',
    'visual',
    'description',
    'technical',
    'specifications',
    'sequence',
    'camera',
    'lighting',
    'subject',
    'animation',
    'narration',
    'timing',
    'code',
    'structure',
    'remotion',
    'tool',
    'duration',
    'timestamp',
    'json',
    'type',
    'clip',
    'video',
    'media',
    'callback',
}


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


def _normalize_clip_identifier(raw_value: str) -> str:
    """Normalize a logical clip identifier for staged asset lookup."""
    normalized = raw_value.replace('\\', '/').lstrip('/')
    basename = normalized.split('/')[-1]
    stem = Path(basename).stem if Path(basename).suffix else basename
    if stem.endswith('_veo'):
        stem = stem[:-4]
    return stem.strip()


def _extract_embedded_veo_clip_ids(data_points: Any) -> List[str]:
    """Return normalized embedded Veo clip ids declared in structured data."""
    if not isinstance(data_points, dict):
        return []

    embedded = data_points.get('embeddedVeoClips')
    if not isinstance(embedded, list):
        return []

    clip_ids: List[str] = []
    for clip_id in embedded:
        if isinstance(clip_id, str) and clip_id.strip():
            normalized = _normalize_clip_identifier(clip_id)
            if normalized and normalized not in clip_ids:
                clip_ids.append(normalized)

    return clip_ids


def _iter_structured_media_candidates(
    raw_value: str,
    embedded_clip_ids: List[str],
) -> List[str]:
    """Return deterministic staged-media lookup candidates for structured refs."""
    candidates: List[str] = []

    def _add(candidate: str) -> None:
        trimmed = candidate.strip()
        if trimmed and trimmed not in candidates:
            candidates.append(trimmed)

    normalized = raw_value.replace('\\', '/').lstrip('/')
    _add(normalized)

    normalized_clip_id = _normalize_clip_identifier(raw_value)
    _add(normalized_clip_id)

    for clip_id in embedded_clip_ids:
        if clip_id == normalized_clip_id:
            _add(clip_id)
            _add(f'{clip_id}.mp4')

    return candidates


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


def _tokenize_media_search_text(raw_value: str) -> List[str]:
    """Return normalized search tokens for fuzzy staged-media matching."""
    tokens: List[str] = []
    for token in re.findall(r'[a-z0-9]+', raw_value.lower()):
        if token in MEDIA_SEARCH_STOPWORDS:
            continue
        if len(token) < 3 and not token.isdigit():
            continue
        if token not in tokens:
            tokens.append(token)
    return tokens


def _iter_available_video_static_paths(remotion_public: str) -> List[str]:
    """List staged video assets under remotion/public for contextual matching."""
    if not remotion_public:
        return []

    search_roots: List[str] = []
    veo_root = os.path.join(remotion_public, 'veo')
    if os.path.isdir(veo_root):
        search_roots.append(veo_root)
    else:
        search_roots.append(remotion_public)

    candidates: List[str] = []
    for search_root in search_roots:
        for root, _, filenames in os.walk(search_root):
            for filename in filenames:
                if Path(filename).suffix.lower() not in VIDEO_EXTENSIONS:
                    continue
                rel_path = os.path.relpath(os.path.join(root, filename), remotion_public)
                normalized = rel_path.replace('\\', '/')
                if normalized not in candidates:
                    candidates.append(normalized)
    return sorted(candidates)


def _resolve_contextual_video_static_path(
    spec_content: str,
    spec_base: str,
    remotion_public: str,
) -> Optional[str]:
    """Resolve alternate staged clip names from clip ids plus spec context."""
    if not spec_content or not remotion_public:
        return None

    data_points = _extract_data_points_json(spec_content)
    token_weights: Dict[str, int] = {}
    exact_stems: List[str] = []

    def _add_tokens(source: str, weight: int) -> None:
        if not source:
            return
        for token in _tokenize_media_search_text(source):
            token_weights[token] = token_weights.get(token, 0) + weight

    def _add_exact_stems(source: str) -> None:
        for stem in _normalize_reference_stems(source):
            normalized = stem.split('/')[-1]
            if normalized and normalized not in exact_stems:
                exact_stems.append(normalized)

    _add_tokens(spec_base, 2)
    _add_exact_stems(spec_base)

    for raw_value in _iter_video_reference_values(spec_content):
        _add_tokens(raw_value, 4)
        _add_exact_stems(raw_value)

    if isinstance(data_points, dict):
        callback_to = data_points.get('callbackTo')
        if isinstance(callback_to, str) and callback_to.strip():
            _add_tokens(callback_to, 3)
            _add_exact_stems(callback_to)

    heading_match = re.search(r'^\s*#\s+(.+)$', spec_content, re.MULTILINE)
    if heading_match:
        _add_tokens(heading_match.group(1), 2)

    _add_tokens(spec_content, 1)

    if not token_weights:
        return None

    best_path: Optional[str] = None
    best_score = 0
    best_overlap = 0
    ambiguous = False

    for candidate in _iter_available_video_static_paths(remotion_public):
        candidate_stem = Path(candidate).stem.lower()
        candidate_tokens = set(_tokenize_media_search_text(candidate_stem))
        if not candidate_tokens:
            continue

        score = 0
        overlap = 0
        for token, weight in token_weights.items():
            if token in candidate_tokens:
                score += weight
                overlap += 1

        for stem in exact_stems:
            if not stem:
                continue
            if candidate_stem == stem:
                score += 100

        if score < 3:
            continue

        if score > best_score or (score == best_score and overlap > best_overlap):
            best_path = candidate
            best_score = score
            best_overlap = overlap
            ambiguous = False
            continue

        if score == best_score and overlap == best_overlap:
            ambiguous = True

    return None if ambiguous else best_path


def _iter_data_point_media_values(data_points: Any) -> List[str]:
    """Collect media-like string values inside structured Data Points JSON."""
    values: List[str] = []
    embedded_clip_ids = _extract_embedded_veo_clip_ids(data_points)

    def _is_explicit_media_value(value: str, key_hint: Optional[str]) -> bool:
        if _is_media_reference_like(value):
            return True
        normalized_clip_id = _normalize_clip_identifier(value)
        if normalized_clip_id in embedded_clip_ids:
            return True
        return key_hint in SOURCE_FIELD_KEYS and bool(value.strip())

    def _walk(value: Any, key_hint: Optional[str] = None) -> None:
        if isinstance(value, dict):
            for raw_key, nested in value.items():
                _walk(nested, str(raw_key).strip().lower().replace('_', '').replace('-', ''))
            return
        if isinstance(value, list):
            for nested in value:
                _walk(nested, key_hint)
            return
        if isinstance(value, str) and _is_explicit_media_value(value, key_hint):
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
    embedded_clip_ids = _extract_embedded_veo_clip_ids(data_points)

    def _is_explicit_media_value(value: str, key_hint: Optional[str]) -> bool:
        if _is_media_reference_like(value):
            return True
        normalized_clip_id = _normalize_clip_identifier(value)
        if normalized_clip_id in embedded_clip_ids:
            return True
        return key_hint in SOURCE_FIELD_KEYS and bool(value.strip())

    def _assign(alias_name: Optional[str], raw_value: str) -> None:
        resolved = None
        for candidate in _iter_structured_media_candidates(raw_value, embedded_clip_ids):
            resolved = _resolve_video_reference_static_path(
                remotion_public,
                candidate,
                reference_aliases,
            )
            if resolved is not None:
                break
        if resolved is None:
            resolved = _resolve_contextual_video_static_path(
                json.dumps(data_points, ensure_ascii=False),
                raw_value,
                remotion_public,
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
                if isinstance(nested, str) and _is_explicit_media_value(nested, key):
                    effective_alias = next_context or alias_name
                    _assign(effective_alias, nested)
                    continue
                _walk(nested, next_context)
            return
        if isinstance(value, list):
            for nested in value:
                _walk(nested, context_alias)
            return
        if isinstance(value, str) and _is_explicit_media_value(value, context_alias):
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


def _has_component_visual_intent(
    project_dir: str,
    section: Dict[str, Any],
    spec_base: str,
) -> bool:
    """Return True when a spec explicitly declares a non-media/component visual."""
    if not project_dir:
        return False

    spec_dir = section.get('specDir') or section['id']
    if not os.path.isabs(spec_dir):
        spec_dir = os.path.join(project_dir, 'specs', str(spec_dir).replace('\\', '/').replace('specs/', '').strip('/'))

    spec_path = os.path.join(spec_dir, f'{spec_base}.md')
    spec_content = _read_text_if_exists(spec_path)
    if not spec_content:
        return False

    lines = spec_content.splitlines()
    first_line = lines[0].strip().lower() if lines else ''
    if '[veo:' in first_line:
        return False
    if '[remotion]' in first_line or '[split:' in first_line:
        return True
    return _extract_data_points_json(spec_content) is not None


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
        elif _has_component_visual_intent(project_dir, section, base):
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


def _declares_explicit_visual_media(spec_content: str) -> bool:
    """Return True when a spec explicitly names media, even if it is unresolved."""
    if not spec_content:
        return False

    if VISUAL_MEDIA_KEY_RE.search(spec_content):
        return True
    if STRUCTURED_VIDEO_FIELD_RE.search(spec_content):
        return True
    if GENERIC_VIDEO_REF_RE.search(spec_content):
        return True

    for rel_path in STATIC_FILE_RE.findall(spec_content):
        if Path(rel_path).suffix.lower() in VIDEO_EXTENSIONS:
            return True

    data_points = _extract_data_points_json(spec_content)
    return bool(data_points is not None and _iter_data_point_media_values(data_points))


def _is_media_driven_visual(
    spec_content: str,
    data_points: Optional[Dict[str, Any]] = None,
) -> bool:
    """Return True when the spec is fundamentally a media clip rather than a component."""
    lines = spec_content.splitlines()
    first_line = lines[0].strip().lower() if lines else ''
    if '[veo:' in first_line:
        return True

    if not isinstance(data_points, dict):
        data_points = _extract_data_points_json(spec_content)

    if not isinstance(data_points, dict):
        return False

    visual_type = data_points.get('type')
    return isinstance(visual_type, str) and visual_type.strip().lower() in MEDIA_DRIVEN_VISUAL_TYPES


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
    data_points = _extract_data_points_json(spec_content)
    media_driven = _is_media_driven_visual(spec_content, data_points)

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

    if media_driven and not explicit_sources:
        contextual_default = _resolve_contextual_video_static_path(
            spec_content,
            spec_base,
            remotion_public,
        )
        if contextual_default is not None:
            explicit = True
            explicit_sources.append(contextual_default)
            aliases.setdefault('defaultSrc', contextual_default)

    if media_driven and not explicit_sources:
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


MEDIA_DRIVEN_VISUAL_TYPES = {
    'veo_clip',
    'video',
    'video_clip',
    'media',
    'broll',
    'raw-media',
    'raw_media',
}

CONTRACT_FIRST_VISUAL_TYPES = {
    'animated_diagram',
    'animated_chart',
    'annotation_overlay',
    'chart_callback',
    'chart_event',
    'code_regeneration',
    'code_transformation',
    'code_visualization',
    'dual_meter_animation',
    'forking_chart',
    'inset_chart',
    'network_graph',
    'pie_chart',
    'quote_card',
    'text_overlay_with_morph',
    'transition',
}

CONTRACT_FIRST_EXACT_OVERRIDE_TYPES = {
    'chart_event',
    'code_regeneration',
    'code_transformation',
    'code_visualization',
    'quote_card',
}

CONTRACT_FIRST_EXACT_OVERRIDE_DIAGRAM_IDS = {
    'code_generation_comparison',
    'embedded_code_document',
    'five_generations',
    'prompt_nozzle',
    'prompt_replaces_review',
    'verilog_synthesis_triple',
}

CONTRACT_FIRST_EXACT_OVERRIDE_CHART_IDS = {
    'compound_debt_curve',
    'maintenance_cost_pie',
}


def _is_structured_title_card(data_points: Dict[str, Any]) -> bool:
    visual_type = data_points.get('type')
    if not isinstance(visual_type, str) or visual_type.strip().lower() != 'title_card':
        return False

    if isinstance(data_points.get('style'), str) and data_points.get('style', '').strip().lower() == 'stillness_beat':
        return True

    return any(
        isinstance(data_points.get(key), str) and data_points.get(key, '').strip()
        for key in ('sectionLabel', 'sectionNumber', 'title', 'titleLine1', 'titleLine2')
    )


def _should_keep_exact_title_card_component(data_points: Dict[str, Any]) -> bool:
    commands = data_points.get('commands')
    if isinstance(commands, list) and any(
        isinstance(command, str) and command.strip()
        for command in commands
    ):
        return True

    chart_id = data_points.get('chartId')
    if isinstance(chart_id, str) and chart_id.strip().lower() == 'final_title_card':
        return True

    return False


def _should_prefer_generated_contract_renderer(
    visual_contract: Dict[str, Any],
    has_exact_component: bool,
) -> bool:
    data_points = visual_contract.get('dataPoints')
    if not isinstance(data_points, dict):
        return False

    if _is_structured_title_card(data_points):
        return not (has_exact_component and _should_keep_exact_title_card_component(data_points))

    visual_type = data_points.get('type')
    if not isinstance(visual_type, str):
        return False

    normalized_type = visual_type.strip().lower()
    diagram_id = data_points.get('diagramId')
    normalized_diagram_id = (
        diagram_id.strip().lower()
        if isinstance(diagram_id, str) and diagram_id.strip()
        else None
    )
    chart_id = data_points.get('chartId')
    normalized_chart_id = (
        chart_id.strip().lower()
        if isinstance(chart_id, str) and chart_id.strip()
        else None
    )

    if normalized_type == 'split_screen':
        return True

    if has_exact_component:
        return (
            normalized_type in CONTRACT_FIRST_EXACT_OVERRIDE_TYPES
            or normalized_diagram_id in CONTRACT_FIRST_EXACT_OVERRIDE_DIAGRAM_IDS
            or normalized_chart_id in CONTRACT_FIRST_EXACT_OVERRIDE_CHART_IDS
        )

    if normalized_type in CONTRACT_FIRST_VISUAL_TYPES:
        return True

    return False


def _allows_inherited_visual_media(spec_content: str) -> bool:
    """Only media-driven visuals may inherit a prior clip implicitly.

    Title cards, beats, code views, and other non-media visuals should not pick
    up the previous spec's clip just because they happen to follow it.
    """
    data_points = _extract_data_points_json(spec_content)
    if not isinstance(data_points, dict):
        return True

    visual_type = data_points.get('type')
    if not isinstance(visual_type, str):
        return True

    return visual_type.strip().lower() in MEDIA_DRIVEN_VISUAL_TYPES


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

        composition_ids = {
            (c if isinstance(c, str) else c.get('id', ''))
            for c in section.get('compositions', [])
        }
        media_manifest = build_visual_media_manifest(
            section,
            project_dir,
            remotion_public,
            component_visual_ids=composition_ids,
        )
        overlay_manifest = build_visual_overlay_manifest(section, project_dir)
        visuals: List[Dict[str, Any]] = []

        def _normalize_parent_reference(raw_parent: Any) -> Optional[str]:
            if not isinstance(raw_parent, str):
                return None
            parent = raw_parent.strip()
            if not parent:
                return None
            parent = re.sub(r'\s+\([^)]*\)\s*$', '', parent).strip()
            return parent or None

        def _normalize_anchor_hint(raw_anchor: Any) -> Optional[Dict[str, Any]]:
            if not isinstance(raw_anchor, dict):
                return None
            anchor_type = raw_anchor.get('type')
            if anchor_type in ('segmentStart', 'segmentEnd'):
                segment_id = raw_anchor.get('segmentId')
                if not isinstance(segment_id, str) or not segment_id:
                    return None
                anchor: Dict[str, Any] = {'type': anchor_type, 'segmentId': segment_id}
                offset_ms = raw_anchor.get('offsetMs')
                if isinstance(offset_ms, (int, float)):
                    anchor['offsetMs'] = int(offset_ms)
                return anchor
            if anchor_type == 'absolute':
                seconds = raw_anchor.get('seconds')
                if not isinstance(seconds, (int, float)):
                    return None
                return {'type': 'absolute', 'seconds': float(seconds)}
            if anchor_type in ('sectionStart', 'sectionEnd'):
                anchor = {'type': anchor_type}
                offset_ms = raw_anchor.get('offsetMs')
                if isinstance(offset_ms, (int, float)):
                    anchor['offsetMs'] = int(offset_ms)
                return anchor
            return None

        for visual_id in visual_ids:
            spec_base = component_base_name(visual_id, section['id'])
            spec_path = os.path.join(spec_dir, f'{spec_base}.md')
            spec_content = _read_text_if_exists(spec_path)
            data_points = _extract_data_points_json(spec_content) if spec_content else None
            has_component = spec_base in composition_ids
            # Extract new manifest fields from data points
            cover_segments = None
            parent_id = None
            lane_hint = None
            start_anchor = None
            end_anchor = None
            start_offset_ms = None
            end_offset_ms = None
            if isinstance(data_points, dict):
                raw_cover = data_points.get('coverSegments') or data_points.get('narrationSegments')
                if isinstance(raw_cover, list):
                    cover_segments = [str(s) for s in raw_cover]
                raw_parent = (
                    data_points.get('embeddedIn')
                    or data_points.get('compositeOver')
                    or data_points.get('usedIn')
                )
                parent_id = _normalize_parent_reference(raw_parent)
                raw_lane = data_points.get('laneHint')
                if isinstance(raw_lane, str) and raw_lane in ('main', 'overlay', 'background'):
                    lane_hint = raw_lane
                elif isinstance(raw_lane, (int, float)):
                    lane_hint = int(raw_lane)
                start_anchor = _normalize_anchor_hint(data_points.get('startAnchor'))
                end_anchor = _normalize_anchor_hint(data_points.get('endAnchor'))
                raw_start_offset = data_points.get('startOffsetMs')
                if isinstance(raw_start_offset, (int, float)):
                    start_offset_ms = int(raw_start_offset)
                raw_end_offset = data_points.get('endOffsetMs')
                if isinstance(raw_end_offset, (int, float)):
                    end_offset_ms = int(raw_end_offset)

            # Infer laneHint from overlayConfig when not explicitly set
            if lane_hint is None and overlay_manifest.get(visual_id):
                lane_hint = 'overlay'

            render_mode = _resolve_visual_render_mode(
                media_manifest.get(visual_id, {}),
                overlay_manifest.get(visual_id),
                has_component=has_component,
            )
            if _should_prefer_generated_contract_renderer(
                {
                    'id': visual_id,
                    'dataPoints': data_points,
                    'renderMode': render_mode,
                },
                has_component,
            ):
                render_mode = 'component'
            if (
                render_mode == 'component'
                and not has_component
                and spec_content
                and _is_media_driven_visual(spec_content, data_points if isinstance(data_points, dict) else None)
            ):
                render_mode = 'raw-media'

            visual_entry: Dict[str, Any] = {
                'id': visual_id,
                'specBaseName': spec_base,
                'specPath': os.path.relpath(spec_path, project_dir).replace('\\', '/') if spec_content else None,
                'dataPoints': data_points,
                'mediaAliases': media_manifest.get(visual_id, {}),
                'overlayConfig': overlay_manifest.get(visual_id),
                'renderMode': render_mode,
            }
            if cover_segments is not None:
                visual_entry['coverSegments'] = cover_segments
            if parent_id is not None:
                visual_entry['parentId'] = parent_id
            if lane_hint is not None:
                visual_entry['laneHint'] = lane_hint
            if start_anchor is not None:
                visual_entry['startAnchor'] = start_anchor
            if end_anchor is not None:
                visual_entry['endAnchor'] = end_anchor
            if start_offset_ms is not None:
                visual_entry['startOffsetMs'] = start_offset_ms
            if end_offset_ms is not None:
                visual_entry['endOffsetMs'] = end_offset_ms

            visuals.append(visual_entry)

        # Second pass: populate children arrays from parentId references
        id_to_visual: Dict[str, Dict[str, Any]] = {v['id']: v for v in visuals}
        for visual in visuals:
            pid = visual.get('parentId')
            if pid and pid in id_to_visual:
                parent = id_to_visual[pid]
                parent.setdefault('children', [])
                if visual['id'] not in parent['children']:
                    parent['children'].append(visual['id'])

        # Third pass: synthesize split-screen media aliases from embedded child clips.
        for visual in visuals:
            data_points = visual.get('dataPoints')
            if not isinstance(data_points, dict):
                continue
            visual_type = data_points.get('type')
            if not isinstance(visual_type, str) or visual_type.strip().lower() != 'split_screen':
                continue

            media_aliases = visual.setdefault('mediaAliases', {})
            if not isinstance(media_aliases, dict):
                media_aliases = {}
                visual['mediaAliases'] = media_aliases

            for child_id in visual.get('children', []):
                child = id_to_visual.get(child_id)
                if not child:
                    continue
                child_data = child.get('dataPoints')
                child_aliases = child.get('mediaAliases')
                if not isinstance(child_aliases, dict):
                    continue
                candidate_src = (
                    child_aliases.get('defaultSrc')
                    or child_aliases.get('backgroundSrc')
                    or child_aliases.get('baseSrc')
                )
                if not isinstance(candidate_src, str) or not candidate_src:
                    continue

                panel = None
                if isinstance(child_data, dict):
                    for key in ('panel', 'side', 'slot'):
                        raw_panel = child_data.get(key)
                        if isinstance(raw_panel, str) and raw_panel.strip():
                            panel = raw_panel.strip().lower()
                            break

                if panel == 'left':
                    media_aliases.setdefault('leftSrc', candidate_src)
                elif panel == 'right':
                    media_aliases.setdefault('rightSrc', candidate_src)

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
            'mediaAliases': visual.get('mediaAliases'),
            'overlayConfig': visual.get('overlayConfig'),
            'renderMode': visual.get('renderMode'),
        }
    return contracts


def resolve_section_component_records(
    section: Dict[str, Any],
    project_dir: str = '',
    remotion_public: str = '',
    remotion_src: str = '',
) -> List[tuple[str, str, str]]:
    """Resolve renderable component visuals using the visual contract as truth.

    Returns tuples of (logical visual id, export name, import path).
    """
    resolved_records: List[tuple[str, str, str]] = []
    seen_visual_ids: set[str] = set()
    contract_first_visual_ids: set[str] = set()
    section_id = str(section.get('id') or '')

    def _has_exact_component(visual_id: str) -> bool:
        return _resolve_existing_comp_import(
            visual_id,
            section_id,
            remotion_src,
            allow_fuzzy=False,
        ) is not None

    def _add_record(visual_id: str, require_existing: bool, allow_fuzzy: bool = True) -> None:
        if not visual_id or visual_id in seen_visual_ids:
            return
        resolved = (
            _resolve_existing_comp_import(visual_id, section_id, remotion_src, allow_fuzzy=allow_fuzzy)
            if require_existing
            else resolve_comp_import(visual_id, section_id, remotion_src)
        )
        if resolved is None:
            return
        export_name, import_path = resolved
        resolved_records.append((visual_id, export_name, import_path))
        seen_visual_ids.add(visual_id)

    require_existing = bool(project_dir and remotion_public and remotion_src)
    if require_existing:
        manifest = build_visual_contract_manifest([section], project_dir, remotion_public)
        section_entry = next(iter(manifest.get('sections', [])), None)
        for visual in section_entry.get('visuals', []) if section_entry else []:
            if visual.get('renderMode') != 'component':
                continue
            visual_id = str(visual.get('id') or '')
            has_exact_component = _has_exact_component(visual_id)
            if _should_prefer_generated_contract_renderer(visual, has_exact_component):
                contract_first_visual_ids.add(visual_id)
                continue
            allow_fuzzy = True
            data_points = visual.get('dataPoints')
            if isinstance(data_points, dict):
                visual_type = data_points.get('type')
                if isinstance(visual_type, str) and visual_type.strip().lower() == 'split_screen' and not has_exact_component:
                    allow_fuzzy = False
            _add_record(visual_id, require_existing=True, allow_fuzzy=allow_fuzzy)

    for composition in section.get('compositions', []):
        comp_id = composition if isinstance(composition, str) else composition.get('id', '')
        if str(comp_id or '') in contract_first_visual_ids:
            continue
        _add_record(str(comp_id or ''), require_existing=require_existing)

    return resolved_records


def build_visual_media_manifest(
    section: Dict[str, Any],
    project_dir: str,
    remotion_public: str,
    fallback_video_src: Optional[str] = None,
    component_visual_ids: Optional[set] = None,
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
        is_component = component_visual_ids and spec_base in component_visual_ids
        aliases: Dict[str, str] = {}

        if os.path.isfile(spec_path):
            spec_content = _read_text_if_exists(spec_path)
            declares_explicit_media = _declares_explicit_visual_media(spec_content)
            aliases, next_default, explicit = _extract_visual_media_aliases(
                spec_content,
                remotion_public,
                inherited_default
                if _allows_inherited_visual_media(spec_content) and not declares_explicit_media
                else None,
                spec_base,
                reference_aliases,
            )
            if explicit:
                saw_explicit_source = True
            if next_default is not None:
                inherited_default = next_default
        elif inherited_default is not None and not is_component:
            aliases = {
                'defaultSrc': inherited_default,
                'backgroundSrc': inherited_default,
                'outputSrc': inherited_default,
                'baseSrc': inherited_default,
            }

        if (
            not aliases
            and not saw_explicit_source
            and fallback_video_src is not None
            and not is_component
            and spec_content
            and _is_media_driven_visual(spec_content)
        ):
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

    data_points = _extract_data_points_json(spec_content)
    overlay = data_points.get('overlay') if isinstance(data_points, dict) else None
    counter = overlay.get('counter') if isinstance(overlay, dict) else None
    if isinstance(counter, dict):
        values = counter.get('values')
        if isinstance(values, list) and any(isinstance(value, (int, float)) for value in values):
            config['counterOverlay'] = True
            position = counter.get('position')
            if isinstance(position, str) and position.strip():
                config['counterPosition'] = position.strip()

    return config or None


def _resolve_visual_render_mode(
    media_aliases: Dict[str, str],
    overlay_config: Optional[Dict[str, Any]],
    has_component: bool = False,
) -> str:
    if has_component:
        return 'component'
    if overlay_config or media_aliases.get('leftSrc') or media_aliases.get('rightSrc'):
        return 'generated-media'
    if media_aliases:
        return 'raw-media'
    return 'component'


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
    project_dir: str = '',
    spec_dir: str = '',
) -> Optional[int]:
    """Best-effort duration discovery from generated component constants.ts."""
    if not remotion_src:
        remotion_src = ''

    _, import_path = resolve_comp_import(comp_id, section_id, remotion_src)
    constants_candidates = [
        os.path.join(remotion_src, import_path, 'constants.ts'),
        os.path.join(remotion_src, f'{import_path}.tsx'),
    ]

    duration_patterns = (
        re.compile(r'\bTOTAL_FRAMES\s*[:=]\s*(\d+)\b'),
        re.compile(r'\bDURATION_FRAMES\s*[:=]\s*(\d+)\b'),
        re.compile(r'\bDURATION_IN_FRAMES\s*[:=]\s*(\d+)\b'),
        re.compile(r'\btotalFrames\s*[:=]\s*(\d+)\b'),
        re.compile(r'\bTOTAL_DURATION_FRAMES\s*[:=]\s*(\d+)\b'),
        re.compile(r'\btotalDuration\s*[:=]\s*(\d+)\b', re.IGNORECASE),
    )

    for candidate in constants_candidates:
        content = _read_text_if_exists(candidate)
        if not content:
            continue
        for duration_re in duration_patterns:
            match = duration_re.search(content)
            if not match:
                continue
            try:
                duration = int(match.group(1))
            except ValueError:
                continue
            if duration > 0:
                return duration

    if project_dir:
        resolved_spec_dir = spec_dir or section_id
        if not os.path.isabs(resolved_spec_dir):
            resolved_spec_dir = os.path.join(
                project_dir,
                'specs',
                str(resolved_spec_dir).replace('\\', '/').replace('specs/', '').strip('/'),
            )

        spec_base = component_base_name(comp_id, section_id)
        spec_path = os.path.join(resolved_spec_dir, f'{spec_base}.md')
        spec_content = _read_text_if_exists(spec_path)
        if spec_content:
            duration_match = re.search(
                r'^\s*[*#>\-\s]*\**Duration:?\**[^\n]*?\b(\d+)\s*frames?\b',
                spec_content,
                re.IGNORECASE | re.MULTILINE,
            )
            if duration_match:
                try:
                    duration = int(duration_match.group(1))
                except ValueError:
                    duration = 0
                if duration > 0:
                    return duration

    return None


def _read_section_duration_from_constants(
    section_id: str,
    remotion_src: str,
) -> Optional[float]:
    """Read SECTION_DURATION_SECONDS from a generated section constants file."""
    if not remotion_src:
        return None

    constants_path = os.path.join(remotion_src, section_id, 'constants.ts')
    content = _read_text_if_exists(constants_path)
    if not content:
        return None

    match = re.search(
        r'\bSECTION_DURATION_SECONDS\s*=\s*([0-9]+(?:\.[0-9]+)?)\b',
        content,
    )
    if not match:
        return None

    try:
        value = float(match.group(1))
    except (TypeError, ValueError):
        return None

    return value if value > 0 else None


def _read_section_duration_from_word_timestamps(
    section_id: str,
    project_dir: str,
) -> Optional[float]:
    """Read the section-local duration from Stage 5 word timestamps."""
    if not project_dir:
        return None

    timestamps_path = os.path.join(
        project_dir,
        'outputs',
        'tts',
        section_id,
        'word_timestamps.json',
    )
    content = _read_text_if_exists(timestamps_path)
    if not content:
        return None

    try:
        parsed = json.loads(content)
    except json.JSONDecodeError:
        return None

    words = parsed if isinstance(parsed, list) else parsed.get('words', [])
    max_end = 0.0
    for word in words:
        if not isinstance(word, dict):
            continue
        end = word.get('end')
        if isinstance(end, (int, float)):
            max_end = max(max_end, float(end))

    return max_end if max_end > 0 else None


def resolve_section_duration_seconds(
    section: Dict[str, Any],
    remotion_src: str = '',
    project_dir: str = '',
) -> float:
    """Resolve stable section duration without trusting render-mutated project.json.

    Priority:
      1. Generated section constants.ts
      2. Stage 5 word_timestamps.json
      3. section.durationSeconds from project.json
    """
    section_id = str(section.get('id') or '')
    if section_id:
        constants_duration = _read_section_duration_from_constants(section_id, remotion_src)
        if constants_duration is not None:
            return constants_duration

        audio_duration = _read_section_duration_from_word_timestamps(section_id, project_dir)
        if audio_duration is not None:
            return audio_duration

    raw_duration = section.get('durationSeconds', 0)
    try:
        return max(0.0, float(raw_duration))
    except (TypeError, ValueError):
        return 0.0


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
    duration_seconds = resolve_section_duration_seconds(
        section,
        remotion_src=remotion_src,
        project_dir=project_dir,
    )
    compositions: List[Dict[str, Any]] = section.get('compositions', [])
    component_records = resolve_section_component_records(
        section,
        project_dir=project_dir,
        remotion_public=remotion_public,
        remotion_src=remotion_src,
    )
    component_visual_ids = {visual_id for visual_id, _, _ in component_records}
    visual_media_manifest = build_visual_media_manifest(
        section,
        project_dir,
        remotion_public,
        direct_video_src if needs_direct_video else None,
        component_visual_ids=component_visual_ids,
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
    needs_generated_media_visual = any(
        bool(visual_overlay_manifest.get(visual_id))
        or bool(aliases.get('leftSrc'))
        or bool(aliases.get('rightSrc'))
        for visual_id, aliases in visual_media_manifest.items()
    )
    needs_generated_contract_visual = any(
        contract.get('renderMode') == 'component' and visual_id not in component_visual_ids
        for visual_id, contract in visual_contract_map.items()
    )

    component_durations: Dict[str, int] = {}
    for comp_id, _, _ in component_records:
        intrinsic_duration = resolve_component_intrinsic_duration_frames(
            comp_id,
            section_id,
            remotion_src,
            project_dir=project_dir,
            spec_dir=section.get('specDir', ''),
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
    if needs_generated_media_visual:
        lines.append('import { GeneratedMediaVisual } from "../_shared/GeneratedMediaVisual";')
    if needs_generated_contract_visual:
        lines.append('import { GeneratedContractVisual } from "../_shared/GeneratedContractVisual";')

    for _, comp_pascal, import_path in component_records:
        lines.append(f'import {{ {comp_pascal} }} from "../{import_path}";')

    lines.append('')
    lines.append('const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {')
    for comp_id, comp_pascal, _ in component_records:
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
    lines.append('  const activeVisuals = VISUAL_SEQUENCE')
    lines.append('    .filter((visual) => frame >= visual.start && frame < visual.end)')
    lines.append('    .slice()')
    lines.append('    .sort((left, right) => ((left.lane ?? 0) - (right.lane ?? 0)) || (left.start - right.start));')
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
    lines.append('                  <VisualMediaProvider media={visualContract?.renderMode === "component" ? null : visualMedia}>')
    lines.append('                    <VisualComponent />')
    lines.append('                  </VisualMediaProvider>')
    lines.append('                </VisualContractProvider>')
    lines.append('              </SlotScaledSequence>')
    if visual_media_manifest:
        lines.append('            ) : visualContract?.renderMode === "component" ? (')
        lines.append('              <VisualContractProvider contract={visualContract}>')
        lines.append('                <VisualMediaProvider media={visualMedia}>')
        lines.append('                  <GeneratedContractVisual />')
        lines.append('                </VisualMediaProvider>')
        lines.append('              </VisualContractProvider>')
        lines.append('            ) : visualMedia?.defaultSrc ? (')
        lines.append('              <VisualContractProvider contract={visualContract}>')
        lines.append('                <VisualMediaProvider media={visualMedia}>')
        if needs_generated_media_visual:
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
        lines.append('            ) : visualContract?.renderMode === "component" ? (')
        lines.append('              <VisualContractProvider contract={visualContract}>')
        lines.append('                <VisualMediaProvider media={visualMedia}>')
        lines.append('                  <GeneratedContractVisual />')
        lines.append('                </VisualMediaProvider>')
        lines.append('              </VisualContractProvider>')
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
    duration_seconds = resolve_section_duration_seconds(
        section,
        remotion_src=remotion_src,
        project_dir=project_dir,
    )
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
    generated_timeline_available = bool(remotion_src) and os.path.isfile(
        os.path.join(remotion_src, section_id, 'constants.ts')
    )
    needs_direct_audio = bool(direct_audio_src) and (
        generated_timeline_available
        or not has_base_component
        or not component_has_audio
    )
    needs_direct_video = (
        bool(direct_video_src)
        and (
            generated_timeline_available
            or not has_base_component
            or not component_has_video
        )
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
    section_component_records: Dict[str, List[tuple[str, str, str]]] = {}
    section_component_lookup: Dict[str, Dict[str, str]] = {}
    section_preview_visual_ids: Dict[str, List[str]] = {}
    needs_generated_contract_preview = False

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
                    'mediaAliases': visual.get('mediaAliases'),
                    'overlayConfig': visual.get('overlayConfig'),
                    'renderMode': visual.get('renderMode'),
                }
                for visual in section_entry.get('visuals', [])
            }

    for section in sections:
        if not project_dir or not remotion_public:
            section_component_records[section['id']] = resolve_section_component_records(
                section,
                remotion_src=remotion_src,
            )
            section_component_lookup[section['id']] = {
                visual_id: export_name
                for visual_id, export_name, _ in section_component_records[section['id']]
            }
            section_preview_visual_ids[section['id']] = [
                visual_id for visual_id, _, _ in section_component_records[section['id']]
            ]
            continue

        fallback_video_src = resolve_direct_video_src(section['id'], remotion_public)
        component_records = resolve_section_component_records(
            section,
            project_dir=project_dir,
            remotion_public=remotion_public,
            remotion_src=remotion_src,
        )
        section_component_records[section['id']] = component_records
        section_component_lookup[section['id']] = {
            visual_id: export_name
            for visual_id, export_name, _ in component_records
        }
        comp_ids = {visual_id for visual_id, _, _ in component_records}
        visual_media_manifest = build_visual_media_manifest(
            section,
            project_dir,
            remotion_public,
            fallback_video_src=fallback_video_src,
            component_visual_ids=comp_ids,
        )
        contract_visuals = section_contract_lookup.get(section['id'], {})
        preview_visual_ids = [
            visual_id
            for visual_id, contract in contract_visuals.items()
            if contract.get('renderMode') == 'component'
        ]
        if not preview_visual_ids:
            preview_visual_ids = [visual_id for visual_id, _, _ in component_records]
        section_preview_visual_ids[section['id']] = preview_visual_ids

        for comp_id in preview_visual_ids:
            media = visual_media_manifest.get(comp_id)
            contract = contract_visuals.get(comp_id)
            if not media and isinstance(contract, dict):
                contract_media = contract.get('mediaAliases')
                if isinstance(contract_media, dict) and contract_media:
                    media = contract_media
            wrapper_key = f'{section["id"]}:{comp_id}'
            export_name = section_component_lookup.get(section['id'], {}).get(comp_id)
            logical_name = export_name or resolve_logical_component_name(comp_id, section['id'])
            preview_wrapper_names[wrapper_key] = f'{logical_name}Preview'
            if export_name is None:
                needs_generated_contract_preview = True
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
    if needs_generated_contract_preview:
        lines.append('import { GeneratedContractVisual } from "./_shared/GeneratedContractVisual";')
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
        for _, comp_pascal, import_path in section_component_records.get(section['id'], []):
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
            preview_visual_ids = section_preview_visual_ids.get(section_id, [])
            for comp_id in preview_visual_ids:
                wrapper_key = f'{section_id}:{comp_id}'
                preview_wrapper_name = preview_wrapper_names.get(wrapper_key)
                if not preview_wrapper_name or preview_wrapper_name in generated_preview_wrappers:
                    continue
                component_export = section_component_lookup.get(section_id, {}).get(comp_id)
                lines.append(f'const {preview_wrapper_name}: React.FC = () => (')
                lines.append(f'  <VisualContractProvider contract={{PREVIEW_VISUAL_CONTRACTS["{section_id}:{comp_id}"] ?? null}}>')
                lines.append(f'    <VisualMediaProvider media={{PREVIEW_VISUAL_MEDIA["{section_id}:{comp_id}"] ?? null}}>')
                if component_export:
                    lines.append(f'      <{component_export} />')
                else:
                    lines.append('      <GeneratedContractVisual />')
                lines.append('    </VisualMediaProvider>')
                lines.append('  </VisualContractProvider>')
                lines.append(');')
                generated_preview_wrappers.add(preview_wrapper_name)
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
        duration_seconds = resolve_section_duration_seconds(
            section,
            remotion_src=remotion_src,
            project_dir=project_dir,
        )
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
        width = section.get('width', default_width)
        height = section.get('height', default_height)
        preview_visual_ids = section_preview_visual_ids.get(section_id)
        if not preview_visual_ids:
            preview_visual_ids = [visual_id for visual_id, _, _ in section_component_records.get(section_id, [])]
        for comp_id in preview_visual_ids:
            wrapper_key = f'{section_id}:{comp_id}'
            if wrapper_key in registered:
                continue
            preview_component = preview_wrapper_names.get(
                wrapper_key,
                section_component_lookup.get(section_id, {}).get(
                    comp_id,
                    resolve_logical_component_name(comp_id, section_id),
                ),
            )
            preview_duration = (
                resolve_component_intrinsic_duration_frames(
                    comp_id,
                    section_id,
                    remotion_src,
                    project_dir=project_dir,
                    spec_dir=section.get('specDir', ''),
                )
                or 150
            )
            remotion_id = resolve_preview_composition_id(comp_id, section_id)
            lines.append(f'      <Composition')
            lines.append(f'        id="{remotion_id}"')
            lines.append(f'        component={{{preview_component}}}')
            lines.append(f'        durationInFrames={{{preview_duration}}}')
            lines.append(f'        fps={{{fps}}}')
            lines.append(f'        width={{{width}}}')
            lines.append(f'        height={{{height}}}')
            lines.append(f'      />')
            registered.add(wrapper_key)

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
    project_dir: str = '',
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
        duration_seconds = resolve_section_duration_seconds(
            section,
            remotion_src=remotion_src,
            project_dir=project_dir,
        )
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
                preview_duration = (
                    resolve_component_intrinsic_duration_frames(
                        comp_id,
                        section_id,
                        remotion_src,
                        project_dir=project_dir,
                        spec_dir=section.get('specDir', ''),
                    )
                    or 150
                )
                comp_block = (
                    f'      <Composition\n'
                    f'        id="{remotion_id}"\n'
                    f'        component={{{comp_pascal}}}\n'
                    f'        durationInFrames={{{preview_duration}}}\n'
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
