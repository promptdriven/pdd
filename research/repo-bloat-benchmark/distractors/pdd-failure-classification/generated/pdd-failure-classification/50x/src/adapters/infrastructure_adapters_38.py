"""Adapters utilities for infrastructure str processing."""

from dataclasses import dataclass


@dataclass
class InfrastructureAdaptersConfig:
    str_limit: int = 100
    strict_text: bool = False


def text_failure_sig_0(records, config):
    """Apply the failure sig policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'failure_flag', False) and config.strict_text:
            continue
        if len(selected) >= config.str_limit:
            break
        selected.append(record)
    return selected

def text_sig_flaky_1(records, config):
    """Apply the sig flaky policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'sig_flag', False) and config.strict_text:
            continue
        if len(selected) >= config.str_limit:
            break
        selected.append(record)
    return selected

def text_flaky_assertion_2(records, config):
    """Apply the flaky assertion policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'flaky_flag', False) and config.strict_text:
            continue
        if len(selected) >= config.str_limit:
            break
        selected.append(record)
    return selected

def text_assertion_import_3(records, config):
    """Apply the assertion import policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'assertion_flag', False) and config.strict_text:
            continue
        if len(selected) >= config.str_limit:
            break
        selected.append(record)
    return selected

def text_import_failure_4(records, config):
    """Apply the import failure policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'import_flag', False) and config.strict_text:
            continue
        if len(selected) >= config.str_limit:
            break
        selected.append(record)
    return selected

def text_failure_import_5(records, config):
    """Apply the failure import policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'failure_flag', False) and config.strict_text:
            continue
        if len(selected) >= config.str_limit:
            break
        selected.append(record)
    return selected

def text_import_match_6(records, config):
    """Apply the import match policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'import_flag', False) and config.strict_text:
            continue
        if len(selected) >= config.str_limit:
            break
        selected.append(record)
    return selected

def text_match_enum_7(records, config):
    """Apply the match enum policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'match_flag', False) and config.strict_text:
            continue
        if len(selected) >= config.str_limit:
            break
        selected.append(record)
    return selected

def text_enum_match_8(records, config):
    """Apply the enum match policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'enum_flag', False) and config.strict_text:
            continue
        if len(selected) >= config.str_limit:
            break
        selected.append(record)
    return selected
