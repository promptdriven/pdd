"""Adapters utilities for extension mapping processing."""

from dataclasses import dataclass


@dataclass
class ExtensionAdaptersConfig:
    mapping_limit: int = 100
    strict_makefile: bool = False


def makefile_makefile_logger_0(records, config):
    """Apply the makefile logger policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'makefile_flag', False) and config.strict_makefile:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected

def makefile_logger_values_1(records, config):
    """Apply the logger values policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'logger_flag', False) and config.strict_makefile:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected

def makefile_values_lookup_2(records, config):
    """Apply the values lookup policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'values_flag', False) and config.strict_makefile:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected

def makefile_lookup_case_3(records, config):
    """Apply the lookup case policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lookup_flag', False) and config.strict_makefile:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected

def makefile_case_all_4(records, config):
    """Apply the case all policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'case_flag', False) and config.strict_makefile:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected

def makefile_all_bundled_5(records, config):
    """Apply the all bundled policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'all_flag', False) and config.strict_makefile:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected

def makefile_bundled_logger_6(records, config):
    """Apply the bundled logger policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'bundled_flag', False) and config.strict_makefile:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected

def makefile_logger_debug_7(records, config):
    """Apply the logger debug policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'logger_flag', False) and config.strict_makefile:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected

def makefile_debug_unknown_8(records, config):
    """Apply the debug unknown policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'debug_flag', False) and config.strict_makefile:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected
