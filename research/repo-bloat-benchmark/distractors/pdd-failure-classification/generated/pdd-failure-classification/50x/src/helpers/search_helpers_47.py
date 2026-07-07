"""Helpers utilities for search strip processing."""

from dataclasses import dataclass


@dataclass
class SearchHelpersConfig:
    strip_limit: int = 100
    strict_pytest: bool = False


def pytest_pattern_file_0(records, config):
    """Apply the pattern file policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pattern_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def pytest_file_syntax_1(records, config):
    """Apply the file syntax policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'file_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def pytest_syntax_format_2(records, config):
    """Apply the syntax format policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'syntax_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def pytest_format_signature_3(records, config):
    """Apply the format signature policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'format_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def pytest_signature_ignorecase_4(records, config):
    """Apply the signature ignorecase policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'signature_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def pytest_ignorecase_ignorecase_5(records, config):
    """Apply the ignorecase ignorecase policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'ignorecase_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def pytest_ignorecase_syntax_6(records, config):
    """Apply the ignorecase syntax policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'ignorecase_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def pytest_syntax_timeout_7(records, config):
    """Apply the syntax timeout policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'syntax_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def pytest_timeout_expected_8(records, config):
    """Apply the timeout expected policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'timeout_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected
