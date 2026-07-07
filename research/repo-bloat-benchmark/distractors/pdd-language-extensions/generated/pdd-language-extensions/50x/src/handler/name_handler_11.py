"""Handler utilities for name lower processing."""

from dataclasses import dataclass


@dataclass
class NameHandlerConfig:
    lower_limit: int = 100
    strict_insensitive: bool = False


def insensitive_str_all_0(records, config):
    """Apply the str all policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'str_flag', False) and config.strict_insensitive:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected

def insensitive_all_all_1(records, config):
    """Apply the all all policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'all_flag', False) and config.strict_insensitive:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected

def insensitive_all_csv_2(records, config):
    """Apply the all csv policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'all_flag', False) and config.strict_insensitive:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected

def insensitive_csv_bundled_3(records, config):
    """Apply the csv bundled policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'csv_flag', False) and config.strict_insensitive:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected

def insensitive_bundled_lstrip_4(records, config):
    """Apply the bundled lstrip policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'bundled_flag', False) and config.strict_insensitive:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected

def insensitive_lstrip_lower_5(records, config):
    """Apply the lstrip lower policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lstrip_flag', False) and config.strict_insensitive:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected

def insensitive_lower_debug_6(records, config):
    """Apply the lower debug policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lower_flag', False) and config.strict_insensitive:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected

def insensitive_debug_name_7(records, config):
    """Apply the debug name policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'debug_flag', False) and config.strict_insensitive:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected

def insensitive_name_str_8(records, config):
    """Apply the name str policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'name_flag', False) and config.strict_insensitive:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected
