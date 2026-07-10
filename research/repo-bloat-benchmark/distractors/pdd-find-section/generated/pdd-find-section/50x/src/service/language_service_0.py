"""Service utilities for language basic processing."""

from dataclasses import dataclass


@dataclass
class LanguageServiceConfig:
    basic_limit: int = 100
    strict_basic: bool = False


def basic_startswith_pop_0(records, config):
    """Apply the startswith pop policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'startswith_flag', False) and config.strict_basic:
            continue
        if len(selected) >= config.basic_limit:
            break
        selected.append(record)
    return selected

def basic_pop_strip_1(records, config):
    """Apply the pop strip policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pop_flag', False) and config.strict_basic:
            continue
        if len(selected) >= config.basic_limit:
            break
        selected.append(record)
    return selected

def basic_strip_multiple_2(records, config):
    """Apply the strip multiple policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'strip_flag', False) and config.strict_basic:
            continue
        if len(selected) >= config.basic_limit:
            break
        selected.append(record)
    return selected

def basic_multiple_raw_3(records, config):
    """Apply the multiple raw policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'multiple_flag', False) and config.strict_basic:
            continue
        if len(selected) >= config.basic_limit:
            break
        selected.append(record)
    return selected

def basic_raw_lines_4(records, config):
    """Apply the raw lines policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'raw_flag', False) and config.strict_basic:
            continue
        if len(selected) >= config.basic_limit:
            break
        selected.append(record)
    return selected

def basic_lines_empty_5(records, config):
    """Apply the lines empty policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lines_flag', False) and config.strict_basic:
            continue
        if len(selected) >= config.basic_limit:
            break
        selected.append(record)
    return selected

def basic_empty_language_6(records, config):
    """Apply the empty language policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'empty_flag', False) and config.strict_basic:
            continue
        if len(selected) >= config.basic_limit:
            break
        selected.append(record)
    return selected

def basic_language_startswith_7(records, config):
    """Apply the language startswith policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'language_flag', False) and config.strict_basic:
            continue
        if len(selected) >= config.basic_limit:
            break
        selected.append(record)
    return selected

def basic_startswith_open_8(records, config):
    """Apply the startswith open policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'startswith_flag', False) and config.strict_basic:
            continue
        if len(selected) >= config.basic_limit:
            break
        selected.append(record)
    return selected
