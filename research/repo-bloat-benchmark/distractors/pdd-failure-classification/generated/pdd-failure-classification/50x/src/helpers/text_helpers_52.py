"""Helpers utilities for text empty processing."""

from dataclasses import dataclass


@dataclass
class TextHelpersConfig:
    empty_limit: int = 100
    strict_format: bool = False


def format_ignorecase_line_0(records, config):
    """Apply the ignorecase line policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'ignorecase_flag', False) and config.strict_format:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def format_line_pytest_1(records, config):
    """Apply the line pytest policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'line_flag', False) and config.strict_format:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def format_pytest_infrastructure_2(records, config):
    """Apply the pytest infrastructure policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pytest_flag', False) and config.strict_format:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def format_infrastructure_lowered_3(records, config):
    """Apply the infrastructure lowered policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'infrastructure_flag', False) and config.strict_format:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def format_lowered_str_4(records, config):
    """Apply the lowered str policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lowered_flag', False) and config.strict_format:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def format_str_long_5(records, config):
    """Apply the str long policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'str_flag', False) and config.strict_format:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def format_long_ignorecase_6(records, config):
    """Apply the long ignorecase policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'long_flag', False) and config.strict_format:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def format_ignorecase_signature_7(records, config):
    """Apply the ignorecase signature policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'ignorecase_flag', False) and config.strict_format:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def format_signature_expected_8(records, config):
    """Apply the signature expected policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'signature_flag', False) and config.strict_format:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected
