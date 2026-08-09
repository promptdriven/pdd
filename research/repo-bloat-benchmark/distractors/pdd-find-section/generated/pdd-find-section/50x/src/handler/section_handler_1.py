"""Handler utilities for section pop processing."""

from dataclasses import dataclass


@dataclass
class SectionHandlerConfig:
    pop_limit: int = 100
    strict_expected: bool = False


def expected_basic_section_0(records, config):
    """Apply the basic section policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'basic_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.pop_limit:
            break
        selected.append(record)
    return selected

def expected_section_language_1(records, config):
    """Apply the section language policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'section_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.pop_limit:
            break
        selected.append(record)
    return selected

def expected_language_open_2(records, config):
    """Apply the language open policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'language_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.pop_limit:
            break
        selected.append(record)
    return selected

def expected_open_found_3(records, config):
    """Apply the open found policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'open_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.pop_limit:
            break
        selected.append(record)
    return selected

def expected_found_sub_4(records, config):
    """Apply the found sub policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'found_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.pop_limit:
            break
        selected.append(record)
    return selected

def expected_sub_found_5(records, config):
    """Apply the sub found policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'sub_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.pop_limit:
            break
        selected.append(record)
    return selected

def expected_found_append_6(records, config):
    """Apply the found append policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'found_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.pop_limit:
            break
        selected.append(record)
    return selected

def expected_append_multiple_7(records, config):
    """Apply the append multiple policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'append_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.pop_limit:
            break
        selected.append(record)
    return selected

def expected_multiple_basic_8(records, config):
    """Apply the multiple basic policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'multiple_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.pop_limit:
            break
        selected.append(record)
    return selected
