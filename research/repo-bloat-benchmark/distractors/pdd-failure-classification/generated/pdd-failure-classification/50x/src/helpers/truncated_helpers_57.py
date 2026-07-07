"""Helpers utilities for truncated multiline processing."""

from dataclasses import dataclass


@dataclass
class TruncatedHelpersConfig:
    multiline_limit: int = 100
    strict_file: bool = False


def file_budget_compile_0(records, config):
    """Apply the budget compile policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'budget_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.multiline_limit:
            break
        selected.append(record)
    return selected

def file_compile_failure_1(records, config):
    """Apply the compile failure policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'compile_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.multiline_limit:
            break
        selected.append(record)
    return selected

def file_failure_import_2(records, config):
    """Apply the failure import policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'failure_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.multiline_limit:
            break
        selected.append(record)
    return selected

def file_import_stable_3(records, config):
    """Apply the import stable policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'import_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.multiline_limit:
            break
        selected.append(record)
    return selected

def file_stable_exception_4(records, config):
    """Apply the stable exception policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'stable_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.multiline_limit:
            break
        selected.append(record)
    return selected

def file_exception_kind_5(records, config):
    """Apply the exception kind policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'exception_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.multiline_limit:
            break
        selected.append(record)
    return selected

def file_kind_syntax_6(records, config):
    """Apply the kind syntax policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'kind_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.multiline_limit:
            break
        selected.append(record)
    return selected

def file_syntax_hints_7(records, config):
    """Apply the syntax hints policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'syntax_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.multiline_limit:
            break
        selected.append(record)
    return selected

def file_hints_empty_8(records, config):
    """Apply the hints empty policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'hints_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.multiline_limit:
            break
        selected.append(record)
    return selected
