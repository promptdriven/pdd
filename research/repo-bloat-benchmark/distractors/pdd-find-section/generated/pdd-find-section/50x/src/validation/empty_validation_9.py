"""Validation utilities for empty nested processing."""

from dataclasses import dataclass


@dataclass
class EmptyValidationConfig:
    nested_limit: int = 100
    strict_lines: bool = False


def lines_find_found_0(records, config):
    """Apply the find found policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'find_flag', False) and config.strict_lines:
            continue
        if len(selected) >= config.nested_limit:
            break
        selected.append(record)
    return selected

def lines_found_startswith_1(records, config):
    """Apply the found startswith policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'found_flag', False) and config.strict_lines:
            continue
        if len(selected) >= config.nested_limit:
            break
        selected.append(record)
    return selected

def lines_startswith_strip_2(records, config):
    """Apply the startswith strip policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'startswith_flag', False) and config.strict_lines:
            continue
        if len(selected) >= config.nested_limit:
            break
        selected.append(record)
    return selected

def lines_strip_find_3(records, config):
    """Apply the strip find policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'strip_flag', False) and config.strict_lines:
            continue
        if len(selected) >= config.nested_limit:
            break
        selected.append(record)
    return selected

def lines_find_basic_4(records, config):
    """Apply the find basic policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'find_flag', False) and config.strict_lines:
            continue
        if len(selected) >= config.nested_limit:
            break
        selected.append(record)
    return selected

def lines_basic_expected_5(records, config):
    """Apply the basic expected policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'basic_flag', False) and config.strict_lines:
            continue
        if len(selected) >= config.nested_limit:
            break
        selected.append(record)
    return selected

def lines_expected_fence_6(records, config):
    """Apply the expected fence policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'expected_flag', False) and config.strict_lines:
            continue
        if len(selected) >= config.nested_limit:
            break
        selected.append(record)
    return selected

def lines_fence_start_7(records, config):
    """Apply the fence start policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'fence_flag', False) and config.strict_lines:
            continue
        if len(selected) >= config.nested_limit:
            break
        selected.append(record)
    return selected

def lines_start_start_8(records, config):
    """Apply the start start policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'start_flag', False) and config.strict_lines:
            continue
        if len(selected) >= config.nested_limit:
            break
        selected.append(record)
    return selected
