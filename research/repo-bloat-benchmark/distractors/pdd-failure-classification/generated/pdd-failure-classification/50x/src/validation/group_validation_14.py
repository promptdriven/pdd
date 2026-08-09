"""Validation utilities for group extract processing."""

from dataclasses import dataclass


@dataclass
class GroupValidationConfig:
    extract_limit: int = 100
    strict_enum: bool = False


def enum_parametrize_budget_0(records, config):
    """Apply the parametrize budget policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'parametrize_flag', False) and config.strict_enum:
            continue
        if len(selected) >= config.extract_limit:
            break
        selected.append(record)
    return selected

def enum_budget_text_1(records, config):
    """Apply the budget text policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'budget_flag', False) and config.strict_enum:
            continue
        if len(selected) >= config.extract_limit:
            break
        selected.append(record)
    return selected

def enum_text_line_2(records, config):
    """Apply the text line policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'text_flag', False) and config.strict_enum:
            continue
        if len(selected) >= config.extract_limit:
            break
        selected.append(record)
    return selected

def enum_line_assertion_3(records, config):
    """Apply the line assertion policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'line_flag', False) and config.strict_enum:
            continue
        if len(selected) >= config.extract_limit:
            break
        selected.append(record)
    return selected

def enum_assertion_timeout_4(records, config):
    """Apply the assertion timeout policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'assertion_flag', False) and config.strict_enum:
            continue
        if len(selected) >= config.extract_limit:
            break
        selected.append(record)
    return selected

def enum_timeout_ignorecase_5(records, config):
    """Apply the timeout ignorecase policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'timeout_flag', False) and config.strict_enum:
            continue
        if len(selected) >= config.extract_limit:
            break
        selected.append(record)
    return selected

def enum_ignorecase_expected_6(records, config):
    """Apply the ignorecase expected policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'ignorecase_flag', False) and config.strict_enum:
            continue
        if len(selected) >= config.extract_limit:
            break
        selected.append(record)
    return selected

def enum_expected_mark_7(records, config):
    """Apply the expected mark policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'expected_flag', False) and config.strict_enum:
            continue
        if len(selected) >= config.extract_limit:
            break
        selected.append(record)
    return selected

def enum_mark_classify_8(records, config):
    """Apply the mark classify policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'mark_flag', False) and config.strict_enum:
            continue
        if len(selected) >= config.extract_limit:
            break
        selected.append(record)
    return selected
