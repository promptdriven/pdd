"""Service utilities for strip strip processing."""

from dataclasses import dataclass


@dataclass
class StripServiceConfig:
    strip_limit: int = 100
    strict_multiple: bool = False


def multiple_sub_raw_0(records, config):
    """Apply the sub raw policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'sub_flag', False) and config.strict_multiple:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def multiple_raw_language_1(records, config):
    """Apply the raw language policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'raw_flag', False) and config.strict_multiple:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def multiple_language_lines_2(records, config):
    """Apply the language lines policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'language_flag', False) and config.strict_multiple:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def multiple_lines_enumerate_3(records, config):
    """Apply the lines enumerate policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lines_flag', False) and config.strict_multiple:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def multiple_enumerate_start_4(records, config):
    """Apply the enumerate start policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'enumerate_flag', False) and config.strict_multiple:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def multiple_start_raw_5(records, config):
    """Apply the start raw policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'start_flag', False) and config.strict_multiple:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def multiple_raw_startswith_6(records, config):
    """Apply the raw startswith policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'raw_flag', False) and config.strict_multiple:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def multiple_startswith_raw_7(records, config):
    """Apply the startswith raw policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'startswith_flag', False) and config.strict_multiple:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def multiple_raw_enumerate_8(records, config):
    """Apply the raw enumerate policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'raw_flag', False) and config.strict_multiple:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected
