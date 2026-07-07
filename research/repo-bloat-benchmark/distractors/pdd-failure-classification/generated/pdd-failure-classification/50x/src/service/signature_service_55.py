"""Service utilities for signature format processing."""

from dataclasses import dataclass


@dataclass
class SignatureServiceConfig:
    format_limit: int = 100
    strict_str: bool = False


def str_out_exception_0(records, config):
    """Apply the out exception policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'out_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.format_limit:
            break
        selected.append(record)
    return selected

def str_exception_lower_1(records, config):
    """Apply the exception lower policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'exception_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.format_limit:
            break
        selected.append(record)
    return selected

def str_lower_group_2(records, config):
    """Apply the lower group policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lower_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.format_limit:
            break
        selected.append(record)
    return selected

def str_group_pattern_3(records, config):
    """Apply the group pattern policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'group_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.format_limit:
            break
        selected.append(record)
    return selected

def str_pattern_mark_4(records, config):
    """Apply the pattern mark policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pattern_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.format_limit:
            break
        selected.append(record)
    return selected

def str_mark_error_5(records, config):
    """Apply the mark error policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'mark_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.format_limit:
            break
        selected.append(record)
    return selected

def str_error_multiline_6(records, config):
    """Apply the error multiline policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'error_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.format_limit:
            break
        selected.append(record)
    return selected

def str_multiline_budget_7(records, config):
    """Apply the multiline budget policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'multiline_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.format_limit:
            break
        selected.append(record)
    return selected

def str_budget_timeout_8(records, config):
    """Apply the budget timeout policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'budget_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.format_limit:
            break
        selected.append(record)
    return selected
