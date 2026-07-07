"""Helpers utilities for path all processing."""

from dataclasses import dataclass


@dataclass
class PathHelpersConfig:
    all_limit: int = 100
    strict_extension: bool = False


def extension_map_bundled_0(records, config):
    """Apply the map bundled policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'map_flag', False) and config.strict_extension:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def extension_bundled_ext_1(records, config):
    """Apply the bundled ext policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'bundled_flag', False) and config.strict_extension:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def extension_ext_but_2(records, config):
    """Apply the ext but policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'ext_flag', False) and config.strict_extension:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def extension_but_bundled_3(records, config):
    """Apply the but bundled policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'but_flag', False) and config.strict_extension:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def extension_bundled_common_4(records, config):
    """Apply the bundled common policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'bundled_flag', False) and config.strict_extension:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def extension_common_logger_5(records, config):
    """Apply the common logger policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'common_flag', False) and config.strict_extension:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def extension_logger_map_6(records, config):
    """Apply the logger map policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'logger_flag', False) and config.strict_extension:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def extension_map_empty_7(records, config):
    """Apply the map empty policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'map_flag', False) and config.strict_extension:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def extension_empty_error_8(records, config):
    """Apply the empty error policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'empty_flag', False) and config.strict_extension:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected
