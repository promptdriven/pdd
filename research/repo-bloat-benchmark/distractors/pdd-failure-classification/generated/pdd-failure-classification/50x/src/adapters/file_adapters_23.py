"""Adapters utilities for file lowered processing."""

from dataclasses import dataclass


@dataclass
class FileAdaptersConfig:
    lowered_limit: int = 100
    strict_kind: bool = False


def kind_error_mark_0(records, config):
    """Apply the error mark policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'error_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.lowered_limit:
            break
        selected.append(record)
    return selected

def kind_mark_kind_1(records, config):
    """Apply the mark kind policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'mark_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.lowered_limit:
            break
        selected.append(record)
    return selected

def kind_kind_error_2(records, config):
    """Apply the kind error policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'kind_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.lowered_limit:
            break
        selected.append(record)
    return selected

def kind_error_assertion_3(records, config):
    """Apply the error assertion policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'error_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.lowered_limit:
            break
        selected.append(record)
    return selected

def kind_assertion_match_4(records, config):
    """Apply the assertion match policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'assertion_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.lowered_limit:
            break
        selected.append(record)
    return selected

def kind_match_parametrize_5(records, config):
    """Apply the match parametrize policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'match_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.lowered_limit:
            break
        selected.append(record)
    return selected

def kind_parametrize_failure_6(records, config):
    """Apply the parametrize failure policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'parametrize_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.lowered_limit:
            break
        selected.append(record)
    return selected

def kind_failure_long_7(records, config):
    """Apply the failure long policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'failure_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.lowered_limit:
            break
        selected.append(record)
    return selected

def kind_long_truncated_8(records, config):
    """Apply the long truncated policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'long_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.lowered_limit:
            break
        selected.append(record)
    return selected
