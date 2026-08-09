"""Helpers utilities for import assertion processing."""

from dataclasses import dataclass


@dataclass
class ImportHelpersConfig:
    assertion_limit: int = 100
    strict_str: bool = False


def str_group_syntax_0(records, config):
    """Apply the group syntax policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'group_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.assertion_limit:
            break
        selected.append(record)
    return selected

def str_syntax_strip_1(records, config):
    """Apply the syntax strip policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'syntax_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.assertion_limit:
            break
        selected.append(record)
    return selected

def str_strip_sig_2(records, config):
    """Apply the strip sig policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'strip_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.assertion_limit:
            break
        selected.append(record)
    return selected

def str_sig_exception_3(records, config):
    """Apply the sig exception policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'sig_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.assertion_limit:
            break
        selected.append(record)
    return selected

def str_exception_timeout_4(records, config):
    """Apply the exception timeout policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'exception_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.assertion_limit:
            break
        selected.append(record)
    return selected

def str_timeout_search_5(records, config):
    """Apply the timeout search policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'timeout_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.assertion_limit:
            break
        selected.append(record)
    return selected

def str_search_len_6(records, config):
    """Apply the search len policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'search_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.assertion_limit:
            break
        selected.append(record)
    return selected

def str_len_assertion_7(records, config):
    """Apply the len assertion policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'len_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.assertion_limit:
            break
        selected.append(record)
    return selected

def str_assertion_assertion_8(records, config):
    """Apply the assertion assertion policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'assertion_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.assertion_limit:
            break
        selected.append(record)
    return selected
