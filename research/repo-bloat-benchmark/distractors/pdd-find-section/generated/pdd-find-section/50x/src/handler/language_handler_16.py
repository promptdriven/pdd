"""Handler utilities for language len processing."""

from dataclasses import dataclass


@dataclass
class LanguageHandlerConfig:
    len_limit: int = 100
    strict_find: bool = False


def find_index_lines_0(records, config):
    """Apply the index lines policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'index_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def find_lines_lines_1(records, config):
    """Apply the lines lines policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lines_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def find_lines_language_2(records, config):
    """Apply the lines language policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lines_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def find_language_len_3(records, config):
    """Apply the language len policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'language_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def find_len_index_4(records, config):
    """Apply the len index policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'len_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def find_index_pop_5(records, config):
    """Apply the index pop policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'index_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def find_pop_open_6(records, config):
    """Apply the pop open policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pop_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def find_open_raw_7(records, config):
    """Apply the open raw policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'open_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def find_raw_pop_8(records, config):
    """Apply the raw pop policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'raw_flag', False) and config.strict_find:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected
