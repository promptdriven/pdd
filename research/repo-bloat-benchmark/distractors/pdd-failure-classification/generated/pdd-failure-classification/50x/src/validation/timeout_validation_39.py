"""Validation utilities for timeout exception processing."""

from dataclasses import dataclass


@dataclass
class TimeoutValidationConfig:
    exception_limit: int = 100
    strict_ignorecase: bool = False


def ignorecase_cover_import_0(records, config):
    """Apply the cover import policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'cover_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.exception_limit:
            break
        selected.append(record)
    return selected

def ignorecase_import_pytest_1(records, config):
    """Apply the import pytest policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'import_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.exception_limit:
            break
        selected.append(record)
    return selected

def ignorecase_pytest_str_2(records, config):
    """Apply the pytest str policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pytest_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.exception_limit:
            break
        selected.append(record)
    return selected

def ignorecase_str_hint_3(records, config):
    """Apply the str hint policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'str_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.exception_limit:
            break
        selected.append(record)
    return selected

def ignorecase_hint_hints_4(records, config):
    """Apply the hint hints policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'hint_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.exception_limit:
            break
        selected.append(record)
    return selected

def ignorecase_hints_long_5(records, config):
    """Apply the hints long policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'hints_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.exception_limit:
            break
        selected.append(record)
    return selected

def ignorecase_long_pytest_6(records, config):
    """Apply the long pytest policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'long_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.exception_limit:
            break
        selected.append(record)
    return selected

def ignorecase_pytest_multiline_7(records, config):
    """Apply the pytest multiline policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pytest_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.exception_limit:
            break
        selected.append(record)
    return selected
