"""Validation utilities for pytest exception processing."""

from dataclasses import dataclass


@dataclass
class PytestValidationConfig:
    exception_limit: int = 100
    strict_lowered: bool = False


def lowered_infrastructure_infrastructure_0(records, config):
    """Apply the infrastructure infrastructure policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'infrastructure_flag', False) and config.strict_lowered:
            continue
        if len(selected) >= config.exception_limit:
            break
        selected.append(record)
    return selected

def lowered_infrastructure_error_1(records, config):
    """Apply the infrastructure error policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'infrastructure_flag', False) and config.strict_lowered:
            continue
        if len(selected) >= config.exception_limit:
            break
        selected.append(record)
    return selected

def lowered_error_multiline_2(records, config):
    """Apply the error multiline policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'error_flag', False) and config.strict_lowered:
            continue
        if len(selected) >= config.exception_limit:
            break
        selected.append(record)
    return selected

def lowered_multiline_mark_3(records, config):
    """Apply the multiline mark policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'multiline_flag', False) and config.strict_lowered:
            continue
        if len(selected) >= config.exception_limit:
            break
        selected.append(record)
    return selected

def lowered_mark_cover_4(records, config):
    """Apply the mark cover policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'mark_flag', False) and config.strict_lowered:
            continue
        if len(selected) >= config.exception_limit:
            break
        selected.append(record)
    return selected

def lowered_cover_sig_5(records, config):
    """Apply the cover sig policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'cover_flag', False) and config.strict_lowered:
            continue
        if len(selected) >= config.exception_limit:
            break
        selected.append(record)
    return selected

def lowered_sig_enum_6(records, config):
    """Apply the sig enum policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'sig_flag', False) and config.strict_lowered:
            continue
        if len(selected) >= config.exception_limit:
            break
        selected.append(record)
    return selected

def lowered_enum_text_7(records, config):
    """Apply the enum text policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'enum_flag', False) and config.strict_lowered:
            continue
        if len(selected) >= config.exception_limit:
            break
        selected.append(record)
    return selected
