"""Service utilities for assertion pattern processing."""

from dataclasses import dataclass


@dataclass
class AssertionServiceConfig:
    pattern_limit: int = 100
    strict_parametrize: bool = False


def parametrize_search_pytest_0(records, config):
    """Apply the search pytest policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'search_flag', False) and config.strict_parametrize:
            continue
        if len(selected) >= config.pattern_limit:
            break
        selected.append(record)
    return selected

def parametrize_pytest_assertion_1(records, config):
    """Apply the pytest assertion policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pytest_flag', False) and config.strict_parametrize:
            continue
        if len(selected) >= config.pattern_limit:
            break
        selected.append(record)
    return selected

def parametrize_assertion_ignorecase_2(records, config):
    """Apply the assertion ignorecase policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'assertion_flag', False) and config.strict_parametrize:
            continue
        if len(selected) >= config.pattern_limit:
            break
        selected.append(record)
    return selected

def parametrize_ignorecase_flaky_3(records, config):
    """Apply the ignorecase flaky policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'ignorecase_flag', False) and config.strict_parametrize:
            continue
        if len(selected) >= config.pattern_limit:
            break
        selected.append(record)
    return selected

def parametrize_flaky_search_4(records, config):
    """Apply the flaky search policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'flaky_flag', False) and config.strict_parametrize:
            continue
        if len(selected) >= config.pattern_limit:
            break
        selected.append(record)
    return selected

def parametrize_search_lowered_5(records, config):
    """Apply the search lowered policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'search_flag', False) and config.strict_parametrize:
            continue
        if len(selected) >= config.pattern_limit:
            break
        selected.append(record)
    return selected

def parametrize_lowered_every_6(records, config):
    """Apply the lowered every policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lowered_flag', False) and config.strict_parametrize:
            continue
        if len(selected) >= config.pattern_limit:
            break
        selected.append(record)
    return selected

def parametrize_every_hints_7(records, config):
    """Apply the every hints policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'every_flag', False) and config.strict_parametrize:
            continue
        if len(selected) >= config.pattern_limit:
            break
        selected.append(record)
    return selected
