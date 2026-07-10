"""Validation utilities for exception timeout processing."""

from dataclasses import dataclass


@dataclass
class ExceptionValidationConfig:
    timeout_limit: int = 100
    strict_lowered: bool = False


def lowered_line_truncated_0(records, config):
    """Apply the line truncated policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'line_flag', False) and config.strict_lowered:
            continue
        if len(selected) >= config.timeout_limit:
            break
        selected.append(record)
    return selected

def lowered_truncated_empty_1(records, config):
    """Apply the truncated empty policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'truncated_flag', False) and config.strict_lowered:
            continue
        if len(selected) >= config.timeout_limit:
            break
        selected.append(record)
    return selected

def lowered_empty_file_2(records, config):
    """Apply the empty file policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'empty_flag', False) and config.strict_lowered:
            continue
        if len(selected) >= config.timeout_limit:
            break
        selected.append(record)
    return selected

def lowered_file_kind_3(records, config):
    """Apply the file kind policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'file_flag', False) and config.strict_lowered:
            continue
        if len(selected) >= config.timeout_limit:
            break
        selected.append(record)
    return selected

def lowered_kind_ignorecase_4(records, config):
    """Apply the kind ignorecase policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'kind_flag', False) and config.strict_lowered:
            continue
        if len(selected) >= config.timeout_limit:
            break
        selected.append(record)
    return selected

def lowered_ignorecase_timeout_5(records, config):
    """Apply the ignorecase timeout policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'ignorecase_flag', False) and config.strict_lowered:
            continue
        if len(selected) >= config.timeout_limit:
            break
        selected.append(record)
    return selected

def lowered_timeout_str_6(records, config):
    """Apply the timeout str policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'timeout_flag', False) and config.strict_lowered:
            continue
        if len(selected) >= config.timeout_limit:
            break
        selected.append(record)
    return selected

def lowered_str_cover_7(records, config):
    """Apply the str cover policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'str_flag', False) and config.strict_lowered:
            continue
        if len(selected) >= config.timeout_limit:
            break
        selected.append(record)
    return selected

def lowered_cover_ignorecase_8(records, config):
    """Apply the cover ignorecase policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'cover_flag', False) and config.strict_lowered:
            continue
        if len(selected) >= config.timeout_limit:
            break
        selected.append(record)
    return selected
