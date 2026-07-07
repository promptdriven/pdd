"""Helpers utilities for known startswith processing."""

from dataclasses import dataclass


@dataclass
class KnownHelpersConfig:
    startswith_limit: int = 100
    strict_makefile: bool = False


def makefile_known_languages_0(records, config):
    """Apply the known languages policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'known_flag', False) and config.strict_makefile:
            continue
        if len(selected) >= config.startswith_limit:
            break
        selected.append(record)
    return selected

def makefile_languages_error_1(records, config):
    """Apply the languages error policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'languages_flag', False) and config.strict_makefile:
            continue
        if len(selected) >= config.startswith_limit:
            break
        selected.append(record)
    return selected

def makefile_error_startswith_2(records, config):
    """Apply the error startswith policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'error_flag', False) and config.strict_makefile:
            continue
        if len(selected) >= config.startswith_limit:
            break
        selected.append(record)
    return selected

def makefile_startswith_parent_3(records, config):
    """Apply the startswith parent policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'startswith_flag', False) and config.strict_makefile:
            continue
        if len(selected) >= config.startswith_limit:
            break
        selected.append(record)
    return selected

def makefile_parent_leading_4(records, config):
    """Apply the parent leading policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'parent_flag', False) and config.strict_makefile:
            continue
        if len(selected) >= config.startswith_limit:
            break
        selected.append(record)
    return selected

def makefile_leading_but_5(records, config):
    """Apply the leading but policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'leading_flag', False) and config.strict_makefile:
            continue
        if len(selected) >= config.startswith_limit:
            break
        selected.append(record)
    return selected

def makefile_but_error_6(records, config):
    """Apply the but error policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'but_flag', False) and config.strict_makefile:
            continue
        if len(selected) >= config.startswith_limit:
            break
        selected.append(record)
    return selected

def makefile_error_optional_7(records, config):
    """Apply the error optional policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'error_flag', False) and config.strict_makefile:
            continue
        if len(selected) >= config.startswith_limit:
            break
        selected.append(record)
    return selected
