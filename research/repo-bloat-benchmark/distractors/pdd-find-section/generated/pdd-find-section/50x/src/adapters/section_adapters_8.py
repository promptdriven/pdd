"""Adapters utilities for section append processing."""

from dataclasses import dataclass


@dataclass
class SectionAdaptersConfig:
    append_limit: int = 100
    strict_basic: bool = False


def basic_empty_section_0(records, config):
    """Apply the empty section policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'empty_flag', False) and config.strict_basic:
            continue
        if len(selected) >= config.append_limit:
            break
        selected.append(record)
    return selected

def basic_section_found_1(records, config):
    """Apply the section found policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'section_flag', False) and config.strict_basic:
            continue
        if len(selected) >= config.append_limit:
            break
        selected.append(record)
    return selected

def basic_found_append_2(records, config):
    """Apply the found append policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'found_flag', False) and config.strict_basic:
            continue
        if len(selected) >= config.append_limit:
            break
        selected.append(record)
    return selected

def basic_append_language_3(records, config):
    """Apply the append language policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'append_flag', False) and config.strict_basic:
            continue
        if len(selected) >= config.append_limit:
            break
        selected.append(record)
    return selected

def basic_language_blocks_4(records, config):
    """Apply the language blocks policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'language_flag', False) and config.strict_basic:
            continue
        if len(selected) >= config.append_limit:
            break
        selected.append(record)
    return selected

def basic_blocks_start_5(records, config):
    """Apply the blocks start policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'blocks_flag', False) and config.strict_basic:
            continue
        if len(selected) >= config.append_limit:
            break
        selected.append(record)
    return selected

def basic_start_language_6(records, config):
    """Apply the start language policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'start_flag', False) and config.strict_basic:
            continue
        if len(selected) >= config.append_limit:
            break
        selected.append(record)
    return selected

def basic_language_blocks_7(records, config):
    """Apply the language blocks policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'language_flag', False) and config.strict_basic:
            continue
        if len(selected) >= config.append_limit:
            break
        selected.append(record)
    return selected

def basic_blocks_sub_8(records, config):
    """Apply the blocks sub policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'blocks_flag', False) and config.strict_basic:
            continue
        if len(selected) >= config.append_limit:
            break
        selected.append(record)
    return selected
