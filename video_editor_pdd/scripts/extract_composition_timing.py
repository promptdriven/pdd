#!/usr/bin/env python3
"""
extract_composition_timing.py

Extracts timing for sub-compositions by keyword-matching composition IDs
against word-level timestamps from the audio narration.

Usage:
    python scripts/extract_composition_timing.py --project-dir . [--duration 5] [--lead 1] [--dry-run]
"""

import argparse
import json
import os
import re
import sys
from typing import Any, Dict, List, Optional, Tuple


# Default duration for sub-compositions (seconds)
DEFAULT_DURATION = 5.0

# Lead time before keyword match (seconds) — composition appears slightly before the word
DEFAULT_LEAD = 1.0

# Composition types that start at the beginning of the section
SECTION_START_TYPES = {'title_card', 'main'}


def load_word_timestamps(section_id: str, project_dir: str) -> Optional[List[Dict[str, Any]]]:
    """Load word timestamps for a section from outputs/tts/{section_id}/word_timestamps.json."""
    timestamps_path = os.path.join(project_dir, 'outputs', 'tts', section_id, 'word_timestamps.json')
    if not os.path.isfile(timestamps_path):
        return None

    with open(timestamps_path, 'r', encoding='utf-8') as f:
        data = json.load(f)

    # Handle both raw array and {words: [...]} formats
    if isinstance(data, dict) and 'words' in data:
        return data['words']
    return data


def extract_keyword(composition_id: str, section_id: str) -> Tuple[str, str]:
    """Extract keyword and composition type from a composition ID.

    Returns (keyword, comp_type) where comp_type is one of:
    'stat_callout', 'split', 'title_card', 'main', 'other'
    """
    # Strip section prefix
    suffix = composition_id.replace(section_id + '_', '', 1)

    if suffix in ('title_card', 'main'):
        return ('', suffix)

    if suffix.startswith('stat_callout_'):
        keyword = suffix.replace('stat_callout_', '', 1)
        return (keyword, 'stat_callout')

    if suffix.startswith('split_'):
        # For split_A_vs_B, extract the most distinctive keyword
        parts = suffix.replace('split_', '', 1).split('_vs_')
        # Use the second part (usually more specific), fallback to first
        keyword = parts[-1] if len(parts) > 1 else parts[0]
        # Remove underscores within keyword parts
        keyword = keyword.replace('_', ' ')
        return (keyword, 'split')

    return (suffix, 'other')


def find_keyword_timestamp(
    keyword: str,
    words: List[Dict[str, Any]],
) -> Optional[float]:
    """Find the first occurrence of a keyword in word timestamps.

    Matching strategy (in order):
    1. Exact word match (case-insensitive, punctuation-stripped)
    2. Keyword contained in a word (4+ char keywords only)
    3. For underscore-separated keywords, try each part (4+ chars)

    Returns the start time of the matching word, or None.
    """
    keyword_lower = keyword.lower()

    # Strategy 1: Exact word match
    keyword_joined = keyword_lower.replace('_', '')
    for w in words:
        word_clean = re.sub(r'[.,!?;:\'"()]+', '', w['word']).lower()
        if word_clean == keyword_joined:
            return w['start']

    # Strategy 2: Keyword contained in word (4+ chars)
    if len(keyword_joined) >= 4:
        for w in words:
            word_clean = re.sub(r'[.,!?;:\'"()]+', '', w['word']).lower()
            if keyword_joined in word_clean:
                return w['start']

    # Strategy 3: Try each part of underscore-separated keywords
    if '_' in keyword_lower:
        parts = [p for p in keyword_lower.split('_') if len(p) >= 4]
        for part in parts:
            for w in words:
                word_clean = re.sub(r'[.,!?;:\'"()]+', '', w['word']).lower()
                if word_clean == part:
                    return w['start']

    return None


def extract_timing_for_section(
    section: Dict[str, Any],
    project_dir: str,
    duration: float = DEFAULT_DURATION,
    lead: float = DEFAULT_LEAD,
) -> List[Dict[str, Any]]:
    """Extract timing for all compositions in a section.

    Returns the updated compositions list with timing fields added.
    """
    section_id = section['id']
    section_duration = section.get('durationSeconds', 0)
    compositions = section.get('compositions', [])

    if not compositions:
        return compositions

    words = load_word_timestamps(section_id, project_dir)

    updated: List[Dict[str, Any]] = []
    for comp in compositions:
        comp_id = comp if isinstance(comp, str) else comp.get('id', '')
        if not comp_id:
            updated.append(comp)
            continue

        # Allow explicit triggerKeyword override from composition config
        trigger_keyword = comp.get('triggerKeyword') if isinstance(comp, dict) else None
        keyword, comp_type = extract_keyword(comp_id, section_id)
        if trigger_keyword:
            keyword = trigger_keyword

        start_seconds: Optional[float] = None
        comp_duration = duration

        if comp_type in SECTION_START_TYPES:
            start_seconds = 0.0
            if comp_type == 'main':
                comp_duration = section_duration
            # title cards default to DEFAULT_DURATION
        elif words and keyword:
            match_time = find_keyword_timestamp(keyword, words)
            if match_time is not None:
                start_seconds = max(0.0, match_time - lead)

        if start_seconds is not None:
            # Clamp duration so it doesn't exceed section length
            if section_duration > 0:
                comp_duration = min(comp_duration, section_duration - start_seconds)
            updated.append({
                'id': comp_id,
                'startSeconds': round(start_seconds, 2),
                'durationSeconds': round(comp_duration, 2),
            })
        else:
            # Could not determine timing — keep as string or original
            updated.append(comp if isinstance(comp, str) else {'id': comp_id})
            print(json.dumps({
                'warning': f'No keyword match for "{comp_id}" (keyword: "{keyword}")',
                'sectionId': section_id,
            }), flush=True)

    return updated


def main() -> None:
    """Extract composition timing from word timestamps and update project.json."""
    parser = argparse.ArgumentParser(
        description='Extract sub-composition timing from narration word timestamps'
    )
    parser.add_argument(
        '--project-dir', default='.', help='Project directory (default: .)'
    )
    parser.add_argument(
        '--duration', type=float, default=DEFAULT_DURATION,
        help=f'Default composition duration in seconds (default: {DEFAULT_DURATION})'
    )
    parser.add_argument(
        '--lead', type=float, default=DEFAULT_LEAD,
        help=f'Lead time before keyword match in seconds (default: {DEFAULT_LEAD})'
    )
    parser.add_argument(
        '--dry-run', action='store_true', default=False,
        help='Print updated compositions without modifying project.json'
    )

    args = parser.parse_args()
    project_dir = args.project_dir

    # Load project.json
    project_path = os.path.join(project_dir, 'project.json')
    if not os.path.isfile(project_path):
        print(json.dumps({'error': f'project.json not found at {project_path}'}), flush=True)
        sys.exit(1)

    with open(project_path, 'r', encoding='utf-8') as f:
        project_data = json.load(f)

    sections = project_data.get('sections', [])
    if not sections:
        print(json.dumps({'warning': 'No sections found'}), flush=True)
        sys.exit(0)

    changed = False
    for section in sections:
        old_compositions = section.get('compositions', [])
        if not old_compositions:
            continue

        updated = extract_timing_for_section(
            section, project_dir, args.duration, args.lead
        )

        if updated != old_compositions:
            section['compositions'] = updated
            changed = True
            print(json.dumps({
                'sectionId': section['id'],
                'status': 'updated',
                'compositions': updated,
            }), flush=True)
        else:
            print(json.dumps({
                'sectionId': section['id'],
                'status': 'unchanged',
            }), flush=True)

    if changed and not args.dry_run:
        with open(project_path, 'w', encoding='utf-8') as f:
            json.dump(project_data, f, indent=2, ensure_ascii=False)
            f.write('\n')
        print(json.dumps({'status': 'project.json updated'}), flush=True)
    elif args.dry_run:
        print(json.dumps({'status': 'dry-run, no changes written'}), flush=True)

    sys.exit(0)


if __name__ == '__main__':
    main()
