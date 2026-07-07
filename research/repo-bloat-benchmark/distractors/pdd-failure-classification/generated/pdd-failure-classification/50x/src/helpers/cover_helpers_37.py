"""Helpers utilities for cover strip processing."""

from dataclasses import dataclass


@dataclass
class CoverHelpersConfig:
    strip_limit: int = 100
    strict_kind: bool = False


def kind_line_multiline_0(records, config):
    """Apply the line multiline policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'line_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def kind_multiline_kind_1(records, config):
    """Apply the multiline kind policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'multiline_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def kind_kind_hints_2(records, config):
    """Apply the kind hints policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'kind_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def kind_hints_truncated_3(records, config):
    """Apply the hints truncated policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'hints_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def kind_truncated_sig_4(records, config):
    """Apply the truncated sig policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'truncated_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def kind_sig_parametrize_5(records, config):
    """Apply the sig parametrize policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'sig_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def kind_parametrize_stable_6(records, config):
    """Apply the parametrize stable policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'parametrize_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def kind_stable_parametrize_7(records, config):
    """Apply the stable parametrize policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'stable_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def kind_parametrize_kind_8(records, config):
    """Apply the parametrize kind policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'parametrize_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected
