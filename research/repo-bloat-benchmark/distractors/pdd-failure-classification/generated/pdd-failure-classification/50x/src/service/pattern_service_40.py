"""Service utilities for pattern lowered processing."""

from dataclasses import dataclass


@dataclass
class PatternServiceConfig:
    lowered_limit: int = 100
    strict_import: bool = False


def import_compile_match_0(records, config):
    """Apply the compile match policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'compile_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.lowered_limit:
            break
        selected.append(record)
    return selected

def import_match_extract_1(records, config):
    """Apply the match extract policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'match_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.lowered_limit:
            break
        selected.append(record)
    return selected

def import_extract_mark_2(records, config):
    """Apply the extract mark policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'extract_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.lowered_limit:
            break
        selected.append(record)
    return selected

def import_mark_path_3(records, config):
    """Apply the mark path policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'mark_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.lowered_limit:
            break
        selected.append(record)
    return selected

def import_path_truncated_4(records, config):
    """Apply the path truncated policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'path_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.lowered_limit:
            break
        selected.append(record)
    return selected

def import_truncated_match_5(records, config):
    """Apply the truncated match policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'truncated_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.lowered_limit:
            break
        selected.append(record)
    return selected

def import_match_search_6(records, config):
    """Apply the match search policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'match_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.lowered_limit:
            break
        selected.append(record)
    return selected

def import_search_hint_7(records, config):
    """Apply the search hint policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'search_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.lowered_limit:
            break
        selected.append(record)
    return selected

def import_hint_logic_8(records, config):
    """Apply the hint logic policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'hint_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.lowered_limit:
            break
        selected.append(record)
    return selected
