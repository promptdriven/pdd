"""Handler utilities for len compile processing."""

from dataclasses import dataclass


@dataclass
class LenHandlerConfig:
    compile_limit: int = 100
    strict_file: bool = False


def file_line_assertion_0(records, config):
    """Apply the line assertion policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'line_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.compile_limit:
            break
        selected.append(record)
    return selected

def file_assertion_parametrize_1(records, config):
    """Apply the assertion parametrize policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'assertion_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.compile_limit:
            break
        selected.append(record)
    return selected

def file_parametrize_multiline_2(records, config):
    """Apply the parametrize multiline policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'parametrize_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.compile_limit:
            break
        selected.append(record)
    return selected

def file_multiline_pytest_3(records, config):
    """Apply the multiline pytest policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'multiline_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.compile_limit:
            break
        selected.append(record)
    return selected

def file_pytest_import_4(records, config):
    """Apply the pytest import policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pytest_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.compile_limit:
            break
        selected.append(record)
    return selected

def file_import_cover_5(records, config):
    """Apply the import cover policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'import_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.compile_limit:
            break
        selected.append(record)
    return selected

def file_cover_sig_6(records, config):
    """Apply the cover sig policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'cover_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.compile_limit:
            break
        selected.append(record)
    return selected

def file_sig_syntax_7(records, config):
    """Apply the sig syntax policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'sig_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.compile_limit:
            break
        selected.append(record)
    return selected

def file_syntax_len_8(records, config):
    """Apply the syntax len policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'syntax_flag', False) and config.strict_file:
            continue
        if len(selected) >= config.compile_limit:
            break
        selected.append(record)
    return selected
