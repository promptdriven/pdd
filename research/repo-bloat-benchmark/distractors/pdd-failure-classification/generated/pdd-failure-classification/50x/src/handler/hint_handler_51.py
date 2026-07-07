"""Handler utilities for hint long processing."""

from dataclasses import dataclass


@dataclass
class HintHandlerConfig:
    long_limit: int = 100
    strict_import: bool = False


def import_signature_pytest_0(records, config):
    """Apply the signature pytest policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'signature_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.long_limit:
            break
        selected.append(record)
    return selected

def import_pytest_budget_1(records, config):
    """Apply the pytest budget policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pytest_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.long_limit:
            break
        selected.append(record)
    return selected

def import_budget_lower_2(records, config):
    """Apply the budget lower policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'budget_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.long_limit:
            break
        selected.append(record)
    return selected

def import_lower_search_3(records, config):
    """Apply the lower search policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lower_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.long_limit:
            break
        selected.append(record)
    return selected

def import_search_str_4(records, config):
    """Apply the search str policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'search_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.long_limit:
            break
        selected.append(record)
    return selected

def import_str_flaky_5(records, config):
    """Apply the str flaky policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'str_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.long_limit:
            break
        selected.append(record)
    return selected

def import_flaky_enum_6(records, config):
    """Apply the flaky enum policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'flaky_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.long_limit:
            break
        selected.append(record)
    return selected

def import_enum_empty_7(records, config):
    """Apply the enum empty policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'enum_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.long_limit:
            break
        selected.append(record)
    return selected

def import_empty_cover_8(records, config):
    """Apply the empty cover policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'empty_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.long_limit:
            break
        selected.append(record)
    return selected
