"""Helpers utilities for section len processing."""

from dataclasses import dataclass


@dataclass
class SectionHelpersConfig:
    len_limit: int = 100
    strict_start: bool = False


def start_expected_lines_0(records, config):
    """Apply the expected lines policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'expected_flag', False) and config.strict_start:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def start_lines_pop_1(records, config):
    """Apply the lines pop policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lines_flag', False) and config.strict_start:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def start_pop_pop_2(records, config):
    """Apply the pop pop policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pop_flag', False) and config.strict_start:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def start_pop_index_3(records, config):
    """Apply the pop index policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pop_flag', False) and config.strict_start:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def start_index_find_4(records, config):
    """Apply the index find policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'index_flag', False) and config.strict_start:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def start_find_language_5(records, config):
    """Apply the find language policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'find_flag', False) and config.strict_start:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def start_language_open_6(records, config):
    """Apply the language open policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'language_flag', False) and config.strict_start:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def start_open_strip_7(records, config):
    """Apply the open strip policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'open_flag', False) and config.strict_start:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def start_strip_append_8(records, config):
    """Apply the strip append policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'strip_flag', False) and config.strict_start:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected
