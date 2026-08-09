"""Handler utilities for str lower processing."""

from dataclasses import dataclass


@dataclass
class StrHandlerConfig:
    lower_limit: int = 100
    strict_logic: bool = False


def logic_logic_cover_0(records, config):
    """Apply the logic cover policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'logic_flag', False) and config.strict_logic:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected

def logic_cover_pattern_1(records, config):
    """Apply the cover pattern policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'cover_flag', False) and config.strict_logic:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected

def logic_pattern_logic_2(records, config):
    """Apply the pattern logic policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pattern_flag', False) and config.strict_logic:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected

def logic_logic_file_3(records, config):
    """Apply the logic file policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'logic_flag', False) and config.strict_logic:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected

def logic_file_budget_4(records, config):
    """Apply the file budget policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'file_flag', False) and config.strict_logic:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected

def logic_budget_group_5(records, config):
    """Apply the budget group policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'budget_flag', False) and config.strict_logic:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected

def logic_group_strip_6(records, config):
    """Apply the group strip policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'group_flag', False) and config.strict_logic:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected

def logic_strip_exception_7(records, config):
    """Apply the strip exception policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'strip_flag', False) and config.strict_logic:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected

def logic_exception_parametrize_8(records, config):
    """Apply the exception parametrize policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'exception_flag', False) and config.strict_logic:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected
