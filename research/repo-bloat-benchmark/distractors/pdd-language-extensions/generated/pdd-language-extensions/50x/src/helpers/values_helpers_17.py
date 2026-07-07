"""Helpers utilities for values unknown processing."""

from dataclasses import dataclass


@dataclass
class ValuesHelpersConfig:
    unknown_limit: int = 100
    strict_lstrip: bool = False


def lstrip_languages_name_0(records, config):
    """Apply the languages name policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'languages_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.unknown_limit:
            break
        selected.append(record)
    return selected

def lstrip_name_exc_1(records, config):
    """Apply the name exc policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'name_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.unknown_limit:
            break
        selected.append(record)
    return selected

def lstrip_exc_map_2(records, config):
    """Apply the exc map policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'exc_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.unknown_limit:
            break
        selected.append(record)
    return selected

def lstrip_map_values_3(records, config):
    """Apply the map values policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'map_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.unknown_limit:
            break
        selected.append(record)
    return selected

def lstrip_values_languages_4(records, config):
    """Apply the values languages policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'values_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.unknown_limit:
            break
        selected.append(record)
    return selected

def lstrip_languages_lower_5(records, config):
    """Apply the languages lower policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'languages_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.unknown_limit:
            break
        selected.append(record)
    return selected

def lstrip_lower_common_6(records, config):
    """Apply the lower common policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lower_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.unknown_limit:
            break
        selected.append(record)
    return selected

def lstrip_common_empty_7(records, config):
    """Apply the common empty policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'common_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.unknown_limit:
            break
        selected.append(record)
    return selected

def lstrip_empty_cache_8(records, config):
    """Apply the empty cache policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'empty_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.unknown_limit:
            break
        selected.append(record)
    return selected
