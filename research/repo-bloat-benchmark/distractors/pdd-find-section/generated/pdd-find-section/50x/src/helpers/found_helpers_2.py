"""Helpers utilities for found append processing."""

from dataclasses import dataclass


@dataclass
class FoundHelpersConfig:
    append_limit: int = 100
    strict_open: bool = False


def open_open_expected_0(records, config):
    """Apply the open expected policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'open_flag', False) and config.strict_open:
            continue
        if len(selected) >= config.append_limit:
            break
        selected.append(record)
    return selected

def open_expected_index_1(records, config):
    """Apply the expected index policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'expected_flag', False) and config.strict_open:
            continue
        if len(selected) >= config.append_limit:
            break
        selected.append(record)
    return selected

def open_index_multiple_2(records, config):
    """Apply the index multiple policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'index_flag', False) and config.strict_open:
            continue
        if len(selected) >= config.append_limit:
            break
        selected.append(record)
    return selected

def open_multiple_strip_3(records, config):
    """Apply the multiple strip policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'multiple_flag', False) and config.strict_open:
            continue
        if len(selected) >= config.append_limit:
            break
        selected.append(record)
    return selected

def open_strip_start_4(records, config):
    """Apply the strip start policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'strip_flag', False) and config.strict_open:
            continue
        if len(selected) >= config.append_limit:
            break
        selected.append(record)
    return selected

def open_start_language_5(records, config):
    """Apply the start language policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'start_flag', False) and config.strict_open:
            continue
        if len(selected) >= config.append_limit:
            break
        selected.append(record)
    return selected

def open_language_enumerate_6(records, config):
    """Apply the language enumerate policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'language_flag', False) and config.strict_open:
            continue
        if len(selected) >= config.append_limit:
            break
        selected.append(record)
    return selected

def open_enumerate_nested_7(records, config):
    """Apply the enumerate nested policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'enumerate_flag', False) and config.strict_open:
            continue
        if len(selected) >= config.append_limit:
            break
        selected.append(record)
    return selected

def open_nested_enumerate_8(records, config):
    """Apply the nested enumerate policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'nested_flag', False) and config.strict_open:
            continue
        if len(selected) >= config.append_limit:
            break
        selected.append(record)
    return selected
