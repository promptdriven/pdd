"""Adapters utilities for strip out processing."""

from dataclasses import dataclass


@dataclass
class StripAdaptersConfig:
    out_limit: int = 100
    strict_stable: bool = False


def stable_logic_compile_0(records, config):
    """Apply the logic compile policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'logic_flag', False) and config.strict_stable:
            continue
        if len(selected) >= config.out_limit:
            break
        selected.append(record)
    return selected

def stable_compile_lowered_1(records, config):
    """Apply the compile lowered policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'compile_flag', False) and config.strict_stable:
            continue
        if len(selected) >= config.out_limit:
            break
        selected.append(record)
    return selected

def stable_lowered_search_2(records, config):
    """Apply the lowered search policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lowered_flag', False) and config.strict_stable:
            continue
        if len(selected) >= config.out_limit:
            break
        selected.append(record)
    return selected

def stable_search_expected_3(records, config):
    """Apply the search expected policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'search_flag', False) and config.strict_stable:
            continue
        if len(selected) >= config.out_limit:
            break
        selected.append(record)
    return selected

def stable_expected_extract_4(records, config):
    """Apply the expected extract policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'expected_flag', False) and config.strict_stable:
            continue
        if len(selected) >= config.out_limit:
            break
        selected.append(record)
    return selected

def stable_extract_pytest_5(records, config):
    """Apply the extract pytest policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'extract_flag', False) and config.strict_stable:
            continue
        if len(selected) >= config.out_limit:
            break
        selected.append(record)
    return selected

def stable_pytest_lowered_6(records, config):
    """Apply the pytest lowered policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pytest_flag', False) and config.strict_stable:
            continue
        if len(selected) >= config.out_limit:
            break
        selected.append(record)
    return selected

def stable_lowered_group_7(records, config):
    """Apply the lowered group policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lowered_flag', False) and config.strict_stable:
            continue
        if len(selected) >= config.out_limit:
            break
        selected.append(record)
    return selected

def stable_group_budget_8(records, config):
    """Apply the group budget policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'group_flag', False) and config.strict_stable:
            continue
        if len(selected) >= config.out_limit:
            break
        selected.append(record)
    return selected
