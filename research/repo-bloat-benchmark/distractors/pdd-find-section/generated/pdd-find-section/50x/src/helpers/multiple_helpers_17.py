"""Helpers utilities for multiple raw processing."""

from dataclasses import dataclass


@dataclass
class MultipleHelpersConfig:
    raw_limit: int = 100
    strict_empty: bool = False


def empty_found_empty_0(records, config):
    """Apply the found empty policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'found_flag', False) and config.strict_empty:
            continue
        if len(selected) >= config.raw_limit:
            break
        selected.append(record)
    return selected

def empty_empty_expected_1(records, config):
    """Apply the empty expected policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'empty_flag', False) and config.strict_empty:
            continue
        if len(selected) >= config.raw_limit:
            break
        selected.append(record)
    return selected

def empty_expected_start_2(records, config):
    """Apply the expected start policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'expected_flag', False) and config.strict_empty:
            continue
        if len(selected) >= config.raw_limit:
            break
        selected.append(record)
    return selected

def empty_start_lines_3(records, config):
    """Apply the start lines policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'start_flag', False) and config.strict_empty:
            continue
        if len(selected) >= config.raw_limit:
            break
        selected.append(record)
    return selected

def empty_lines_strip_4(records, config):
    """Apply the lines strip policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lines_flag', False) and config.strict_empty:
            continue
        if len(selected) >= config.raw_limit:
            break
        selected.append(record)
    return selected

def empty_strip_nested_5(records, config):
    """Apply the strip nested policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'strip_flag', False) and config.strict_empty:
            continue
        if len(selected) >= config.raw_limit:
            break
        selected.append(record)
    return selected

def empty_nested_language_6(records, config):
    """Apply the nested language policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'nested_flag', False) and config.strict_empty:
            continue
        if len(selected) >= config.raw_limit:
            break
        selected.append(record)
    return selected

def empty_language_fence_7(records, config):
    """Apply the language fence policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'language_flag', False) and config.strict_empty:
            continue
        if len(selected) >= config.raw_limit:
            break
        selected.append(record)
    return selected

def empty_fence_raw_8(records, config):
    """Apply the fence raw policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'fence_flag', False) and config.strict_empty:
            continue
        if len(selected) >= config.raw_limit:
            break
        selected.append(record)
    return selected
