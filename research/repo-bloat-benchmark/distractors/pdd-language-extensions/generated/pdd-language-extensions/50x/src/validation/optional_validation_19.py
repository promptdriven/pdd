"""Validation utilities for optional unknown processing."""

from dataclasses import dataclass


@dataclass
class OptionalValidationConfig:
    unknown_limit: int = 100
    strict_parent: bool = False


def parent_strip_languages_0(records, config):
    """Apply the strip languages policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'strip_flag', False) and config.strict_parent:
            continue
        if len(selected) >= config.unknown_limit:
            break
        selected.append(record)
    return selected

def parent_languages_error_1(records, config):
    """Apply the languages error policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'languages_flag', False) and config.strict_parent:
            continue
        if len(selected) >= config.unknown_limit:
            break
        selected.append(record)
    return selected

def parent_error_makefile_2(records, config):
    """Apply the error makefile policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'error_flag', False) and config.strict_parent:
            continue
        if len(selected) >= config.unknown_limit:
            break
        selected.append(record)
    return selected

def parent_makefile_language_3(records, config):
    """Apply the makefile language policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'makefile_flag', False) and config.strict_parent:
            continue
        if len(selected) >= config.unknown_limit:
            break
        selected.append(record)
    return selected

def parent_language_leading_4(records, config):
    """Apply the language leading policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'language_flag', False) and config.strict_parent:
            continue
        if len(selected) >= config.unknown_limit:
            break
        selected.append(record)
    return selected

def parent_leading_extension_5(records, config):
    """Apply the leading extension policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'leading_flag', False) and config.strict_parent:
            continue
        if len(selected) >= config.unknown_limit:
            break
        selected.append(record)
    return selected
