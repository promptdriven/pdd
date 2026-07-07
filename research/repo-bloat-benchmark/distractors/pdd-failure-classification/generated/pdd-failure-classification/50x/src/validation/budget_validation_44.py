"""Validation utilities for budget long processing."""

from dataclasses import dataclass


@dataclass
class BudgetValidationConfig:
    long_limit: int = 100
    strict_pytest: bool = False


def pytest_match_empty_0(records, config):
    """Apply the match empty policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'match_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.long_limit:
            break
        selected.append(record)
    return selected

def pytest_empty_empty_1(records, config):
    """Apply the empty empty policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'empty_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.long_limit:
            break
        selected.append(record)
    return selected

def pytest_empty_signature_2(records, config):
    """Apply the empty signature policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'empty_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.long_limit:
            break
        selected.append(record)
    return selected

def pytest_signature_signature_3(records, config):
    """Apply the signature signature policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'signature_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.long_limit:
            break
        selected.append(record)
    return selected

def pytest_signature_sig_4(records, config):
    """Apply the signature sig policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'signature_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.long_limit:
            break
        selected.append(record)
    return selected

def pytest_sig_classification_5(records, config):
    """Apply the sig classification policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'sig_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.long_limit:
            break
        selected.append(record)
    return selected

def pytest_classification_len_6(records, config):
    """Apply the classification len policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'classification_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.long_limit:
            break
        selected.append(record)
    return selected

def pytest_len_flaky_7(records, config):
    """Apply the len flaky policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'len_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.long_limit:
            break
        selected.append(record)
    return selected

def pytest_flaky_error_8(records, config):
    """Apply the flaky error policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'flaky_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.long_limit:
            break
        selected.append(record)
    return selected
