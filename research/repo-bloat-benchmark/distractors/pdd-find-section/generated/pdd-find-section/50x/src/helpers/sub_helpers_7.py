"""Helpers utilities for sub pop processing."""

from dataclasses import dataclass


@dataclass
class SubHelpersConfig:
    pop_limit: int = 100
    strict_index: bool = False


def index_empty_start_0(records, config):
    """Apply the empty start policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'empty_flag', False) and config.strict_index:
            continue
        if len(selected) >= config.pop_limit:
            break
        selected.append(record)
    return selected

def index_start_find_1(records, config):
    """Apply the start find policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'start_flag', False) and config.strict_index:
            continue
        if len(selected) >= config.pop_limit:
            break
        selected.append(record)
    return selected

def index_find_pop_2(records, config):
    """Apply the find pop policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'find_flag', False) and config.strict_index:
            continue
        if len(selected) >= config.pop_limit:
            break
        selected.append(record)
    return selected

def index_pop_pop_3(records, config):
    """Apply the pop pop policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pop_flag', False) and config.strict_index:
            continue
        if len(selected) >= config.pop_limit:
            break
        selected.append(record)
    return selected

def index_pop_sub_4(records, config):
    """Apply the pop sub policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pop_flag', False) and config.strict_index:
            continue
        if len(selected) >= config.pop_limit:
            break
        selected.append(record)
    return selected

def index_sub_strip_5(records, config):
    """Apply the sub strip policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'sub_flag', False) and config.strict_index:
            continue
        if len(selected) >= config.pop_limit:
            break
        selected.append(record)
    return selected

def index_strip_multiple_6(records, config):
    """Apply the strip multiple policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'strip_flag', False) and config.strict_index:
            continue
        if len(selected) >= config.pop_limit:
            break
        selected.append(record)
    return selected

def index_multiple_language_7(records, config):
    """Apply the multiple language policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'multiple_flag', False) and config.strict_index:
            continue
        if len(selected) >= config.pop_limit:
            break
        selected.append(record)
    return selected

def index_language_language_8(records, config):
    """Apply the language language policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'language_flag', False) and config.strict_index:
            continue
        if len(selected) >= config.pop_limit:
            break
        selected.append(record)
    return selected
