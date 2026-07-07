"""Service utilities for strip syntax processing."""

from dataclasses import dataclass


@dataclass
class StripServiceConfig:
    syntax_limit: int = 100
    strict_lower: bool = False


def lower_path_import_0(records, config):
    """Apply the path import policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'path_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected

def lower_import_failure_1(records, config):
    """Apply the import failure policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'import_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected

def lower_failure_hints_2(records, config):
    """Apply the failure hints policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'failure_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected

def lower_hints_str_3(records, config):
    """Apply the hints str policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'hints_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected

def lower_str_import_4(records, config):
    """Apply the str import policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'str_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected

def lower_import_pattern_5(records, config):
    """Apply the import pattern policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'import_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected

def lower_pattern_mark_6(records, config):
    """Apply the pattern mark policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pattern_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected

def lower_mark_stable_7(records, config):
    """Apply the mark stable policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'mark_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected

def lower_stable_file_8(records, config):
    """Apply the stable file policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'stable_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected
