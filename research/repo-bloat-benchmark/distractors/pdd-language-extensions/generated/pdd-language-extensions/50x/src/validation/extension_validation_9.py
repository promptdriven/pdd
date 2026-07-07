"""Validation utilities for extension strip processing."""

from dataclasses import dataclass


@dataclass
class ExtensionValidationConfig:
    strip_limit: int = 100
    strict_startswith: bool = False


def startswith_dict_insensitive_0(records, config):
    """Apply the dict insensitive policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'dict_flag', False) and config.strict_startswith:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def startswith_insensitive_ext_1(records, config):
    """Apply the insensitive ext policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'insensitive_flag', False) and config.strict_startswith:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def startswith_ext_leading_2(records, config):
    """Apply the ext leading policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'ext_flag', False) and config.strict_startswith:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def startswith_leading_logger_3(records, config):
    """Apply the leading logger policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'leading_flag', False) and config.strict_startswith:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def startswith_logger_debug_4(records, config):
    """Apply the logger debug policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'logger_flag', False) and config.strict_startswith:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def startswith_debug_bundled_5(records, config):
    """Apply the debug bundled policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'debug_flag', False) and config.strict_startswith:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def startswith_bundled_cache_6(records, config):
    """Apply the bundled cache policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'bundled_flag', False) and config.strict_startswith:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def startswith_cache_insensitive_7(records, config):
    """Apply the cache insensitive policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'cache_flag', False) and config.strict_startswith:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected
