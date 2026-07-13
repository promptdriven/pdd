"""Service utilities for language basic processing."""

from dataclasses import dataclass


@dataclass
class LanguageServiceConfig:
    basic_limit: int = 100
    strict_basic: bool = False


def basic_startswith_pop_0(records, config):
    """Apply the startswith pop policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'startswith_flag', False) and config.strict_basic:
            continue
        if len(selected) >= config.basic_limit:
            break
        selected.append(record)
    return selected

def basic_pop_strip_1(records, config):
    """Apply the pop strip policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pop_flag', False) and config.strict_basic:
            continue
        if len(selected) >= config.basic_limit:
            break
        selected.append(record)
    return selected

def basic_strip_multiple_2(records, config):
    """Apply the strip multiple policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'strip_flag', False) and config.strict_basic:
            continue
        if len(selected) >= config.basic_limit:
            break
        selected.append(record)
    return selected
