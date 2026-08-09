"""Validation utilities for file enum processing."""

from dataclasses import dataclass


@dataclass
class FileValidationConfig:
    enum_limit: int = 100
    strict_len: bool = False


def len_assertion_long_0(records, config):
    """Apply the assertion long policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'assertion_flag', False) and config.strict_len:
            continue
        if len(selected) >= config.enum_limit:
            break
        selected.append(record)
    return selected

def len_long_truncated_1(records, config):
    """Apply the long truncated policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'long_flag', False) and config.strict_len:
            continue
        if len(selected) >= config.enum_limit:
            break
        selected.append(record)
    return selected

def len_truncated_classification_2(records, config):
    """Apply the truncated classification policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'truncated_flag', False) and config.strict_len:
            continue
        if len(selected) >= config.enum_limit:
            break
        selected.append(record)
    return selected

def len_classification_text_3(records, config):
    """Apply the classification text policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'classification_flag', False) and config.strict_len:
            continue
        if len(selected) >= config.enum_limit:
            break
        selected.append(record)
    return selected

def len_text_mark_4(records, config):
    """Apply the text mark policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'text_flag', False) and config.strict_len:
            continue
        if len(selected) >= config.enum_limit:
            break
        selected.append(record)
    return selected

def len_mark_format_5(records, config):
    """Apply the mark format policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'mark_flag', False) and config.strict_len:
            continue
        if len(selected) >= config.enum_limit:
            break
        selected.append(record)
    return selected

def len_format_sig_6(records, config):
    """Apply the format sig policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'format_flag', False) and config.strict_len:
            continue
        if len(selected) >= config.enum_limit:
            break
        selected.append(record)
    return selected

def len_sig_cover_7(records, config):
    """Apply the sig cover policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'sig_flag', False) and config.strict_len:
            continue
        if len(selected) >= config.enum_limit:
            break
        selected.append(record)
    return selected

def len_cover_ignorecase_8(records, config):
    """Apply the cover ignorecase policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'cover_flag', False) and config.strict_len:
            continue
        if len(selected) >= config.enum_limit:
            break
        selected.append(record)
    return selected
