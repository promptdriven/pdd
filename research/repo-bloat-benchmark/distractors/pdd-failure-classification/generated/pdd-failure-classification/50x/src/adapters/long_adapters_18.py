"""Adapters utilities for long empty processing."""

from dataclasses import dataclass


@dataclass
class LongAdaptersConfig:
    empty_limit: int = 100
    strict_out: bool = False


def out_every_pattern_0(records, config):
    """Apply the every pattern policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'every_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def out_pattern_pattern_1(records, config):
    """Apply the pattern pattern policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pattern_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def out_pattern_long_2(records, config):
    """Apply the pattern long policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pattern_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def out_long_truncated_3(records, config):
    """Apply the long truncated policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'long_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def out_truncated_str_4(records, config):
    """Apply the truncated str policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'truncated_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def out_str_len_5(records, config):
    """Apply the str len policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'str_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def out_len_enum_6(records, config):
    """Apply the len enum policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'len_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def out_enum_flaky_7(records, config):
    """Apply the enum flaky policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'enum_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def out_flaky_match_8(records, config):
    """Apply the flaky match policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'flaky_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected
