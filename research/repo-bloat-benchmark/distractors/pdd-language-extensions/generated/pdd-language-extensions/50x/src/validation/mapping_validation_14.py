"""Validation utilities for mapping all processing."""

from dataclasses import dataclass


@dataclass
class MappingValidationConfig:
    all_limit: int = 100
    strict_row: bool = False


def row_language_but_0(records, config):
    """Apply the language but policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'language_flag', False) and config.strict_row:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def row_but_dot_1(records, config):
    """Apply the but dot policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'but_flag', False) and config.strict_row:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def row_dot_unknown_2(records, config):
    """Apply the dot unknown policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'dot_flag', False) and config.strict_row:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def row_unknown_file_3(records, config):
    """Apply the unknown file policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'unknown_flag', False) and config.strict_row:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def row_file_bundled_4(records, config):
    """Apply the file bundled policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'file_flag', False) and config.strict_row:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def row_bundled_bundled_5(records, config):
    """Apply the bundled bundled policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'bundled_flag', False) and config.strict_row:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def row_bundled_optional_6(records, config):
    """Apply the bundled optional policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'bundled_flag', False) and config.strict_row:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def row_optional_logger_7(records, config):
    """Apply the optional logger policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'optional_flag', False) and config.strict_row:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def row_logger_makefile_8(records, config):
    """Apply the logger makefile policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'logger_flag', False) and config.strict_row:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected
