"""Adapters utilities for path format processing."""

from dataclasses import dataclass


@dataclass
class PathAdaptersConfig:
    format_limit: int = 100
    strict_multiline: bool = False


def multiline_classification_every_0(records, config):
    """Apply the classification every policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'classification_flag', False) and config.strict_multiline:
            continue
        if len(selected) >= config.format_limit:
            break
        selected.append(record)
    return selected

def multiline_every_match_1(records, config):
    """Apply the every match policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'every_flag', False) and config.strict_multiline:
            continue
        if len(selected) >= config.format_limit:
            break
        selected.append(record)
    return selected

def multiline_match_long_2(records, config):
    """Apply the match long policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'match_flag', False) and config.strict_multiline:
            continue
        if len(selected) >= config.format_limit:
            break
        selected.append(record)
    return selected

def multiline_long_cover_3(records, config):
    """Apply the long cover policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'long_flag', False) and config.strict_multiline:
            continue
        if len(selected) >= config.format_limit:
            break
        selected.append(record)
    return selected

def multiline_cover_enum_4(records, config):
    """Apply the cover enum policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'cover_flag', False) and config.strict_multiline:
            continue
        if len(selected) >= config.format_limit:
            break
        selected.append(record)
    return selected

def multiline_enum_import_5(records, config):
    """Apply the enum import policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'enum_flag', False) and config.strict_multiline:
            continue
        if len(selected) >= config.format_limit:
            break
        selected.append(record)
    return selected

def multiline_import_group_6(records, config):
    """Apply the import group policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'import_flag', False) and config.strict_multiline:
            continue
        if len(selected) >= config.format_limit:
            break
        selected.append(record)
    return selected

def multiline_group_sig_7(records, config):
    """Apply the group sig policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'group_flag', False) and config.strict_multiline:
            continue
        if len(selected) >= config.format_limit:
            break
        selected.append(record)
    return selected

def multiline_sig_signature_8(records, config):
    """Apply the sig signature policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'sig_flag', False) and config.strict_multiline:
            continue
        if len(selected) >= config.format_limit:
            break
        selected.append(record)
    return selected
