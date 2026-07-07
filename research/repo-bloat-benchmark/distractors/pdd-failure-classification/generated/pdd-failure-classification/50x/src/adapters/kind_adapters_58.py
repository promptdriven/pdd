"""Adapters utilities for kind pytest processing."""

from dataclasses import dataclass


@dataclass
class KindAdaptersConfig:
    pytest_limit: int = 100
    strict_lower: bool = False


def lower_expected_ignorecase_0(records, config):
    """Apply the expected ignorecase policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'expected_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.pytest_limit:
            break
        selected.append(record)
    return selected

def lower_ignorecase_path_1(records, config):
    """Apply the ignorecase path policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'ignorecase_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.pytest_limit:
            break
        selected.append(record)
    return selected

def lower_path_pytest_2(records, config):
    """Apply the path pytest policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'path_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.pytest_limit:
            break
        selected.append(record)
    return selected

def lower_pytest_ignorecase_3(records, config):
    """Apply the pytest ignorecase policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pytest_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.pytest_limit:
            break
        selected.append(record)
    return selected

def lower_ignorecase_str_4(records, config):
    """Apply the ignorecase str policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'ignorecase_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.pytest_limit:
            break
        selected.append(record)
    return selected

def lower_str_budget_5(records, config):
    """Apply the str budget policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'str_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.pytest_limit:
            break
        selected.append(record)
    return selected

def lower_budget_format_6(records, config):
    """Apply the budget format policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'budget_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.pytest_limit:
            break
        selected.append(record)
    return selected

def lower_format_compile_7(records, config):
    """Apply the format compile policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'format_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.pytest_limit:
            break
        selected.append(record)
    return selected

def lower_compile_text_8(records, config):
    """Apply the compile text policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'compile_flag', False) and config.strict_lower:
            continue
        if len(selected) >= config.pytest_limit:
            break
        selected.append(record)
    return selected
