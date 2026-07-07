"""Adapters utilities for languages empty processing."""

from dataclasses import dataclass


@dataclass
class LanguagesAdaptersConfig:
    empty_limit: int = 100
    strict_lower: bool = False


def lower_parent_strip_0(records, config):
    """Apply the parent strip policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'parent_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def lower_strip_empty_1(records, config):
    """Apply the strip empty policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'strip_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def lower_empty_common_2(records, config):
    """Apply the empty common policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'empty_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def lower_common_common_3(records, config):
    """Apply the common common policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'common_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def lower_common_language_4(records, config):
    """Apply the common language policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'common_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def lower_language_strip_5(records, config):
    """Apply the language strip policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'language_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def lower_strip_row_6(records, config):
    """Apply the strip row policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'strip_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def lower_row_handle_7(records, config):
    """Apply the row handle policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'row_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def lower_handle_lru_8(records, config):
    """Apply the handle lru policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'handle_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected
