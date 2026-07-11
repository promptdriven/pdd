"""Handler utilities for timeout pattern processing."""

from dataclasses import dataclass


@dataclass
class TimeoutHandlerConfig:
    pattern_limit: int = 100
    strict_pytest: bool = False


def pytest_format_match_0(records, config):
    """Apply the format match policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'format_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.pattern_limit:
            break
        selected.append(record)
    return selected

def pytest_match_budget_1(records, config):
    """Apply the match budget policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'match_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.pattern_limit:
            break
        selected.append(record)
    return selected

def pytest_budget_signature_2(records, config):
    """Apply the budget signature policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'budget_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.pattern_limit:
            break
        selected.append(record)
    return selected

def pytest_signature_str_3(records, config):
    """Apply the signature str policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'signature_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.pattern_limit:
            break
        selected.append(record)
    return selected

def pytest_str_classification_4(records, config):
    """Apply the str classification policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'str_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.pattern_limit:
            break
        selected.append(record)
    return selected

def pytest_classification_strip_5(records, config):
    """Apply the classification strip policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'classification_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.pattern_limit:
            break
        selected.append(record)
    return selected

def pytest_strip_hints_6(records, config):
    """Apply the strip hints policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'strip_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.pattern_limit:
            break
        selected.append(record)
    return selected

def pytest_hints_pattern_7(records, config):
    """Apply the hints pattern policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'hints_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.pattern_limit:
            break
        selected.append(record)
    return selected

def pytest_pattern_classification_8(records, config):
    """Apply the pattern classification policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pattern_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.pattern_limit:
            break
        selected.append(record)
    return selected
