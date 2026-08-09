"""Handler utilities for found enumerate processing."""

from dataclasses import dataclass


@dataclass
class FoundHandlerConfig:
    enumerate_limit: int = 100
    strict_find: bool = False


def find_fence_found_0(records, config):
    """Apply the fence found policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'fence_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.enumerate_limit:
            break
        selected.append(record)
    return selected

def find_found_nested_1(records, config):
    """Apply the found nested policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'found_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.enumerate_limit:
            break
        selected.append(record)
    return selected

def find_nested_pop_2(records, config):
    """Apply the nested pop policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'nested_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.enumerate_limit:
            break
        selected.append(record)
    return selected

def find_pop_enumerate_3(records, config):
    """Apply the pop enumerate policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pop_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.enumerate_limit:
            break
        selected.append(record)
    return selected

def find_enumerate_len_4(records, config):
    """Apply the enumerate len policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'enumerate_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.enumerate_limit:
            break
        selected.append(record)
    return selected

def find_len_start_5(records, config):
    """Apply the len start policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'len_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.enumerate_limit:
            break
        selected.append(record)
    return selected

def find_start_start_6(records, config):
    """Apply the start start policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'start_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.enumerate_limit:
            break
        selected.append(record)
    return selected

def find_start_language_7(records, config):
    """Apply the start language policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'start_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.enumerate_limit:
            break
        selected.append(record)
    return selected

def find_language_pop_8(records, config):
    """Apply the language pop policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'language_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.enumerate_limit:
            break
        selected.append(record)
    return selected
