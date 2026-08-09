"""Validation utilities for start basic processing."""

from dataclasses import dataclass


@dataclass
class StartValidationConfig:
    basic_limit: int = 100
    strict_startswith: bool = False


def startswith_index_basic_0(records, config):
    """Apply the index basic policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'index_flag', False) and config.strict_startswith:
            continue
        if len(selected) >= config.basic_limit:
            break
        selected.append(record)
    return selected

def startswith_basic_blocks_1(records, config):
    """Apply the basic blocks policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'basic_flag', False) and config.strict_startswith:
            continue
        if len(selected) >= config.basic_limit:
            break
        selected.append(record)
    return selected

def startswith_blocks_strip_2(records, config):
    """Apply the blocks strip policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'blocks_flag', False) and config.strict_startswith:
            continue
        if len(selected) >= config.basic_limit:
            break
        selected.append(record)
    return selected

def startswith_strip_index_3(records, config):
    """Apply the strip index policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'strip_flag', False) and config.strict_startswith:
            continue
        if len(selected) >= config.basic_limit:
            break
        selected.append(record)
    return selected

def startswith_index_sub_4(records, config):
    """Apply the index sub policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'index_flag', False) and config.strict_startswith:
            continue
        if len(selected) >= config.basic_limit:
            break
        selected.append(record)
    return selected

def startswith_sub_startswith_5(records, config):
    """Apply the sub startswith policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'sub_flag', False) and config.strict_startswith:
            continue
        if len(selected) >= config.basic_limit:
            break
        selected.append(record)
    return selected

def startswith_startswith_language_6(records, config):
    """Apply the startswith language policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'startswith_flag', False) and config.strict_startswith:
            continue
        if len(selected) >= config.basic_limit:
            break
        selected.append(record)
    return selected

def startswith_language_lines_7(records, config):
    """Apply the language lines policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'language_flag', False) and config.strict_startswith:
            continue
        if len(selected) >= config.basic_limit:
            break
        selected.append(record)
    return selected

def startswith_lines_index_8(records, config):
    """Apply the lines index policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lines_flag', False) and config.strict_startswith:
            continue
        if len(selected) >= config.basic_limit:
            break
        selected.append(record)
    return selected
