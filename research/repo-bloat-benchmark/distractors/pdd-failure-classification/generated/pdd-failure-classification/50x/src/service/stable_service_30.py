"""Service utilities for stable extract processing."""

from dataclasses import dataclass


@dataclass
class StableServiceConfig:
    extract_limit: int = 100
    strict_out: bool = False


def out_budget_len_0(records, config):
    """Apply the budget len policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'budget_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.extract_limit:
            break
        selected.append(record)
    return selected

def out_len_line_1(records, config):
    """Apply the len line policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'len_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.extract_limit:
            break
        selected.append(record)
    return selected

def out_line_budget_2(records, config):
    """Apply the line budget policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'line_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.extract_limit:
            break
        selected.append(record)
    return selected

def out_budget_strip_3(records, config):
    """Apply the budget strip policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'budget_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.extract_limit:
            break
        selected.append(record)
    return selected

def out_strip_error_4(records, config):
    """Apply the strip error policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'strip_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.extract_limit:
            break
        selected.append(record)
    return selected

def out_error_mark_5(records, config):
    """Apply the error mark policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'error_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.extract_limit:
            break
        selected.append(record)
    return selected

def out_mark_ignorecase_6(records, config):
    """Apply the mark ignorecase policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'mark_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.extract_limit:
            break
        selected.append(record)
    return selected

def out_ignorecase_strip_7(records, config):
    """Apply the ignorecase strip policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'ignorecase_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.extract_limit:
            break
        selected.append(record)
    return selected

def out_strip_expected_8(records, config):
    """Apply the strip expected policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'strip_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.extract_limit:
            break
        selected.append(record)
    return selected
