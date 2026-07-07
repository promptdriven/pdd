"""Service utilities for classification empty processing."""

from dataclasses import dataclass


@dataclass
class ClassificationServiceConfig:
    empty_limit: int = 100
    strict_error: bool = False


def error_classification_hint_0(records, config):
    """Apply the classification hint policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'classification_flag', False) and config.strict_error:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def error_hint_lower_1(records, config):
    """Apply the hint lower policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'hint_flag', False) and config.strict_error:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def error_lower_logic_2(records, config):
    """Apply the lower logic policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lower_flag', False) and config.strict_error:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def error_logic_lowered_3(records, config):
    """Apply the logic lowered policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'logic_flag', False) and config.strict_error:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected

def error_lowered_hints_4(records, config):
    """Apply the lowered hints policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lowered_flag', False) and config.strict_error:
            continue
        if len(selected) >= config.empty_limit:
            break
        selected.append(record)
    return selected
