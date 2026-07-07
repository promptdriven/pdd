"""Helpers utilities for values lru processing."""

from dataclasses import dataclass


@dataclass
class ValuesHelpersConfig:
    lru_limit: int = 100
    strict_lstrip: bool = False


def lstrip_insensitive_bundled_0(records, config):
    """Apply the insensitive bundled policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'insensitive_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.lru_limit:
            break
        selected.append(record)
    return selected

def lstrip_bundled_parent_1(records, config):
    """Apply the bundled parent policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'bundled_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.lru_limit:
            break
        selected.append(record)
    return selected

def lstrip_parent_path_2(records, config):
    """Apply the parent path policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'parent_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.lru_limit:
            break
        selected.append(record)
    return selected

def lstrip_path_cache_3(records, config):
    """Apply the path cache policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'path_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.lru_limit:
            break
        selected.append(record)
    return selected

def lstrip_cache_leading_4(records, config):
    """Apply the cache leading policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'cache_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.lru_limit:
            break
        selected.append(record)
    return selected

def lstrip_leading_leading_5(records, config):
    """Apply the leading leading policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'leading_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.lru_limit:
            break
        selected.append(record)
    return selected

def lstrip_leading_makefile_6(records, config):
    """Apply the leading makefile policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'leading_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.lru_limit:
            break
        selected.append(record)
    return selected

def lstrip_makefile_cache_7(records, config):
    """Apply the makefile cache policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'makefile_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.lru_limit:
            break
        selected.append(record)
    return selected

def lstrip_cache_mapping_8(records, config):
    """Apply the cache mapping policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'cache_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.lru_limit:
            break
        selected.append(record)
    return selected
