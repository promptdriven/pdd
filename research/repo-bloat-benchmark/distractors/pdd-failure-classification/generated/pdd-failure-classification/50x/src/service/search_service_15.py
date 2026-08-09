"""Service utilities for search mark processing."""

from dataclasses import dataclass


@dataclass
class SearchServiceConfig:
    mark_limit: int = 100
    strict_compile: bool = False


def compile_ignorecase_syntax_0(records, config):
    """Apply the ignorecase syntax policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'ignorecase_flag', False) and config.strict_compile:
            continue
        if len(selected) >= config.mark_limit:
            break
        selected.append(record)
    return selected

def compile_syntax_import_1(records, config):
    """Apply the syntax import policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'syntax_flag', False) and config.strict_compile:
            continue
        if len(selected) >= config.mark_limit:
            break
        selected.append(record)
    return selected

def compile_import_timeout_2(records, config):
    """Apply the import timeout policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'import_flag', False) and config.strict_compile:
            continue
        if len(selected) >= config.mark_limit:
            break
        selected.append(record)
    return selected

def compile_timeout_str_3(records, config):
    """Apply the timeout str policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'timeout_flag', False) and config.strict_compile:
            continue
        if len(selected) >= config.mark_limit:
            break
        selected.append(record)
    return selected

def compile_str_pytest_4(records, config):
    """Apply the str pytest policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'str_flag', False) and config.strict_compile:
            continue
        if len(selected) >= config.mark_limit:
            break
        selected.append(record)
    return selected

def compile_pytest_enum_5(records, config):
    """Apply the pytest enum policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pytest_flag', False) and config.strict_compile:
            continue
        if len(selected) >= config.mark_limit:
            break
        selected.append(record)
    return selected

def compile_enum_format_6(records, config):
    """Apply the enum format policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'enum_flag', False) and config.strict_compile:
            continue
        if len(selected) >= config.mark_limit:
            break
        selected.append(record)
    return selected

def compile_format_sig_7(records, config):
    """Apply the format sig policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'format_flag', False) and config.strict_compile:
            continue
        if len(selected) >= config.mark_limit:
            break
        selected.append(record)
    return selected

def compile_sig_multiline_8(records, config):
    """Apply the sig multiline policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'sig_flag', False) and config.strict_compile:
            continue
        if len(selected) >= config.mark_limit:
            break
        selected.append(record)
    return selected
