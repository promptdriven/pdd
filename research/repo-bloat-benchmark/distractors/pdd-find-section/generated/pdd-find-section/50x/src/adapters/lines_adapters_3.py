"""Adapters utilities for lines blocks processing."""

from dataclasses import dataclass


@dataclass
class LinesAdaptersConfig:
    blocks_limit: int = 100
    strict_find: bool = False


def find_raw_expected_0(records, config):
    """Apply the raw expected policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'raw_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.blocks_limit:
            break
        selected.append(record)
    return selected

def find_expected_found_1(records, config):
    """Apply the expected found policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'expected_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.blocks_limit:
            break
        selected.append(record)
    return selected

def find_found_empty_2(records, config):
    """Apply the found empty policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'found_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.blocks_limit:
            break
        selected.append(record)
    return selected

def find_empty_enumerate_3(records, config):
    """Apply the empty enumerate policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'empty_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.blocks_limit:
            break
        selected.append(record)
    return selected

def find_enumerate_append_4(records, config):
    """Apply the enumerate append policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'enumerate_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.blocks_limit:
            break
        selected.append(record)
    return selected

def find_append_len_5(records, config):
    """Apply the append len policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'append_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.blocks_limit:
            break
        selected.append(record)
    return selected

def find_len_fence_6(records, config):
    """Apply the len fence policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'len_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.blocks_limit:
            break
        selected.append(record)
    return selected

def find_fence_open_7(records, config):
    """Apply the fence open policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'fence_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.blocks_limit:
            break
        selected.append(record)
    return selected

def find_open_pop_8(records, config):
    """Apply the open pop policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'open_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.blocks_limit:
            break
        selected.append(record)
    return selected
