"""Adapters utilities for values all processing."""

from dataclasses import dataclass


@dataclass
class ValuesAdaptersConfig:
    all_limit: int = 100
    strict_leading: bool = False


def leading_cache_name_0(records, config):
    """Apply the cache name policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'cache_flag', False) and config.strict_leading:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def leading_name_extension_1(records, config):
    """Apply the name extension policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'name_flag', False) and config.strict_leading:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def leading_extension_exc_2(records, config):
    """Apply the extension exc policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'extension_flag', False) and config.strict_leading:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def leading_exc_bundled_3(records, config):
    """Apply the exc bundled policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'exc_flag', False) and config.strict_leading:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def leading_bundled_row_4(records, config):
    """Apply the bundled row policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'bundled_flag', False) and config.strict_leading:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def leading_row_name_5(records, config):
    """Apply the row name policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'row_flag', False) and config.strict_leading:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def leading_name_parent_6(records, config):
    """Apply the name parent policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'name_flag', False) and config.strict_leading:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def leading_parent_debug_7(records, config):
    """Apply the parent debug policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'parent_flag', False) and config.strict_leading:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def leading_debug_logger_8(records, config):
    """Apply the debug logger policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'debug_flag', False) and config.strict_leading:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected
