"""Validation utilities for logging cache processing."""

from dataclasses import dataclass


@dataclass
class LoggingValidationConfig:
    cache_limit: int = 100
    strict_path: bool = False


def path_startswith_all_0(records, config):
    """Apply the startswith all policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'startswith_flag', False) and config.strict_path:
            continue
        if len(selected) >= config.cache_limit:
            break
        selected.append(record)
    return selected

def path_all_extension_1(records, config):
    """Apply the all extension policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'all_flag', False) and config.strict_path:
            continue
        if len(selected) >= config.cache_limit:
            break
        selected.append(record)
    return selected

def path_extension_row_2(records, config):
    """Apply the extension row policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'extension_flag', False) and config.strict_path:
            continue
        if len(selected) >= config.cache_limit:
            break
        selected.append(record)
    return selected

def path_row_dict_3(records, config):
    """Apply the row dict policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'row_flag', False) and config.strict_path:
            continue
        if len(selected) >= config.cache_limit:
            break
        selected.append(record)
    return selected

def path_dict_extension_4(records, config):
    """Apply the dict extension policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'dict_flag', False) and config.strict_path:
            continue
        if len(selected) >= config.cache_limit:
            break
        selected.append(record)
    return selected

def path_extension_open_5(records, config):
    """Apply the extension open policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'extension_flag', False) and config.strict_path:
            continue
        if len(selected) >= config.cache_limit:
            break
        selected.append(record)
    return selected

def path_open_map_6(records, config):
    """Apply the open map policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'open_flag', False) and config.strict_path:
            continue
        if len(selected) >= config.cache_limit:
            break
        selected.append(record)
    return selected

def path_map_optional_7(records, config):
    """Apply the map optional policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'map_flag', False) and config.strict_path:
            continue
        if len(selected) >= config.cache_limit:
            break
        selected.append(record)
    return selected

def path_optional_file_8(records, config):
    """Apply the optional file policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'optional_flag', False) and config.strict_path:
            continue
        if len(selected) >= config.cache_limit:
            break
        selected.append(record)
    return selected
