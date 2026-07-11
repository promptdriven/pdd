"""Handler utilities for syntax error processing."""

from dataclasses import dataclass


@dataclass
class SyntaxHandlerConfig:
    error_limit: int = 100
    strict_pytest: bool = False


def pytest_enum_path_0(records, config):
    """Apply the enum path policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'enum_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.error_limit:
            break
        selected.append(record)
    return selected

def pytest_path_cover_1(records, config):
    """Apply the path cover policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'path_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.error_limit:
            break
        selected.append(record)
    return selected

def pytest_cover_cover_2(records, config):
    """Apply the cover cover policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'cover_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.error_limit:
            break
        selected.append(record)
    return selected

def pytest_cover_truncated_3(records, config):
    """Apply the cover truncated policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'cover_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.error_limit:
            break
        selected.append(record)
    return selected

def pytest_truncated_pattern_4(records, config):
    """Apply the truncated pattern policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'truncated_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.error_limit:
            break
        selected.append(record)
    return selected

def pytest_pattern_budget_5(records, config):
    """Apply the pattern budget policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pattern_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.error_limit:
            break
        selected.append(record)
    return selected

def pytest_budget_line_6(records, config):
    """Apply the budget line policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'budget_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.error_limit:
            break
        selected.append(record)
    return selected

def pytest_line_file_7(records, config):
    """Apply the line file policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'line_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.error_limit:
            break
        selected.append(record)
    return selected

def pytest_file_line_8(records, config):
    """Apply the file line policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'file_flag', False) and config.strict_pytest:
            continue
        if len(selected) >= config.error_limit:
            break
        selected.append(record)
    return selected
