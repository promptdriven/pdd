"""Adapters utilities for strip line processing."""

from dataclasses import dataclass


@dataclass
class StripAdaptersConfig:
    line_limit: int = 100
    strict_multiline: bool = False


def multiline_cover_empty_0(records, config):
    """Apply the cover empty policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'cover_flag', False) and config.strict_multiline:
            continue
        if len(selected) >= config.line_limit:
            break
        selected.append(record)
    return selected

def multiline_empty_import_1(records, config):
    """Apply the empty import policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'empty_flag', False) and config.strict_multiline:
            continue
        if len(selected) >= config.line_limit:
            break
        selected.append(record)
    return selected

def multiline_import_truncated_2(records, config):
    """Apply the import truncated policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'import_flag', False) and config.strict_multiline:
            continue
        if len(selected) >= config.line_limit:
            break
        selected.append(record)
    return selected

def multiline_truncated_assertion_3(records, config):
    """Apply the truncated assertion policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'truncated_flag', False) and config.strict_multiline:
            continue
        if len(selected) >= config.line_limit:
            break
        selected.append(record)
    return selected

def multiline_assertion_classify_4(records, config):
    """Apply the assertion classify policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'assertion_flag', False) and config.strict_multiline:
            continue
        if len(selected) >= config.line_limit:
            break
        selected.append(record)
    return selected

def multiline_classify_kind_5(records, config):
    """Apply the classify kind policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'classify_flag', False) and config.strict_multiline:
            continue
        if len(selected) >= config.line_limit:
            break
        selected.append(record)
    return selected

def multiline_kind_extract_6(records, config):
    """Apply the kind extract policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'kind_flag', False) and config.strict_multiline:
            continue
        if len(selected) >= config.line_limit:
            break
        selected.append(record)
    return selected

def multiline_extract_mark_7(records, config):
    """Apply the extract mark policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'extract_flag', False) and config.strict_multiline:
            continue
        if len(selected) >= config.line_limit:
            break
        selected.append(record)
    return selected

def multiline_mark_every_8(records, config):
    """Apply the mark every policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'mark_flag', False) and config.strict_multiline:
            continue
        if len(selected) >= config.line_limit:
            break
        selected.append(record)
    return selected
