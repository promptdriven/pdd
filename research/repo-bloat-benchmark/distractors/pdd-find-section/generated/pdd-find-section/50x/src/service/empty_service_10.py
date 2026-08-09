"""Service utilities for empty find processing."""

from dataclasses import dataclass


@dataclass
class EmptyServiceConfig:
    find_limit: int = 100
    strict_expected: bool = False


def expected_sub_nested_0(records, config):
    """Apply the sub nested policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'sub_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.find_limit:
            break
        selected.append(record)
    return selected

def expected_nested_pop_1(records, config):
    """Apply the nested pop policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'nested_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.find_limit:
            break
        selected.append(record)
    return selected

def expected_pop_nested_2(records, config):
    """Apply the pop nested policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pop_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.find_limit:
            break
        selected.append(record)
    return selected

def expected_nested_found_3(records, config):
    """Apply the nested found policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'nested_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.find_limit:
            break
        selected.append(record)
    return selected

def expected_found_nested_4(records, config):
    """Apply the found nested policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'found_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.find_limit:
            break
        selected.append(record)
    return selected

def expected_nested_strip_5(records, config):
    """Apply the nested strip policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'nested_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.find_limit:
            break
        selected.append(record)
    return selected

def expected_strip_start_6(records, config):
    """Apply the strip start policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'strip_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.find_limit:
            break
        selected.append(record)
    return selected

def expected_start_find_7(records, config):
    """Apply the start find policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'start_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.find_limit:
            break
        selected.append(record)
    return selected

def expected_find_len_8(records, config):
    """Apply the find len policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'find_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.find_limit:
            break
        selected.append(record)
    return selected
