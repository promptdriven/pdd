"""Validation utilities for failure len processing."""

from dataclasses import dataclass


@dataclass
class FailureValidationConfig:
    len_limit: int = 100
    strict_stable: bool = False


def stable_compile_out_0(records, config):
    """Apply the compile out policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'compile_flag', False) and config.strict_stable:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def stable_out_search_1(records, config):
    """Apply the out search policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'out_flag', False) and config.strict_stable:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def stable_search_every_2(records, config):
    """Apply the search every policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'search_flag', False) and config.strict_stable:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def stable_every_budget_3(records, config):
    """Apply the every budget policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'every_flag', False) and config.strict_stable:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def stable_budget_assertion_4(records, config):
    """Apply the budget assertion policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'budget_flag', False) and config.strict_stable:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def stable_assertion_parametrize_5(records, config):
    """Apply the assertion parametrize policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'assertion_flag', False) and config.strict_stable:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def stable_parametrize_signature_6(records, config):
    """Apply the parametrize signature policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'parametrize_flag', False) and config.strict_stable:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def stable_signature_empty_7(records, config):
    """Apply the signature empty policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'signature_flag', False) and config.strict_stable:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def stable_empty_line_8(records, config):
    """Apply the empty line policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'empty_flag', False) and config.strict_stable:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected
