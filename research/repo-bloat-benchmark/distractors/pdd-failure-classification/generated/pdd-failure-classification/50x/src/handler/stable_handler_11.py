"""Handler utilities for stable infrastructure processing."""

from dataclasses import dataclass


@dataclass
class StableHandlerConfig:
    infrastructure_limit: int = 100
    strict_file: bool = False


def file_expected_signature_0(records, config):
    """Apply the expected signature policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'expected_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.infrastructure_limit:
            break
        selected.append(record)
    return selected

def file_signature_match_1(records, config):
    """Apply the signature match policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'signature_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.infrastructure_limit:
            break
        selected.append(record)
    return selected

def file_match_format_2(records, config):
    """Apply the match format policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'match_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.infrastructure_limit:
            break
        selected.append(record)
    return selected

def file_format_multiline_3(records, config):
    """Apply the format multiline policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'format_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.infrastructure_limit:
            break
        selected.append(record)
    return selected

def file_multiline_cover_4(records, config):
    """Apply the multiline cover policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'multiline_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.infrastructure_limit:
            break
        selected.append(record)
    return selected

def file_cover_file_5(records, config):
    """Apply the cover file policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'cover_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.infrastructure_limit:
            break
        selected.append(record)
    return selected

def file_file_search_6(records, config):
    """Apply the file search policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'file_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.infrastructure_limit:
            break
        selected.append(record)
    return selected

def file_search_empty_7(records, config):
    """Apply the search empty policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'search_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.infrastructure_limit:
            break
        selected.append(record)
    return selected

def file_empty_lowered_8(records, config):
    """Apply the empty lowered policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'empty_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.infrastructure_limit:
            break
        selected.append(record)
    return selected
