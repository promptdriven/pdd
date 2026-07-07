"""Validation utilities for pattern str processing."""

from dataclasses import dataclass


@dataclass
class PatternValidationConfig:
    str_limit: int = 100
    strict_import: bool = False


def import_strip_lowered_0(records, config):
    """Apply the strip lowered policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'strip_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.str_limit:
            break
        selected.append(record)
    return selected

def import_lowered_kind_1(records, config):
    """Apply the lowered kind policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lowered_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.str_limit:
            break
        selected.append(record)
    return selected

def import_kind_truncated_2(records, config):
    """Apply the kind truncated policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'kind_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.str_limit:
            break
        selected.append(record)
    return selected

def import_truncated_sig_3(records, config):
    """Apply the truncated sig policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'truncated_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.str_limit:
            break
        selected.append(record)
    return selected

def import_sig_match_4(records, config):
    """Apply the sig match policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'sig_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.str_limit:
            break
        selected.append(record)
    return selected

def import_match_cover_5(records, config):
    """Apply the match cover policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'match_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.str_limit:
            break
        selected.append(record)
    return selected

def import_cover_classify_6(records, config):
    """Apply the cover classify policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'cover_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.str_limit:
            break
        selected.append(record)
    return selected

def import_classify_mark_7(records, config):
    """Apply the classify mark policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'classify_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.str_limit:
            break
        selected.append(record)
    return selected

def import_mark_error_8(records, config):
    """Apply the mark error policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'mark_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.str_limit:
            break
        selected.append(record)
    return selected
