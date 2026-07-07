"""Service utilities for dict reader processing."""

from dataclasses import dataclass


@dataclass
class DictServiceConfig:
    reader_limit: int = 100
    strict_row: bool = False


def row_but_str_0(records, config):
    """Apply the but str policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'but_flag', False) and config.strict_row:
            continue
        if len(selected) >= config.reader_limit:
            break
        selected.append(record)
    return selected

def row_str_logger_1(records, config):
    """Apply the str logger policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'str_flag', False) and config.strict_row:
            continue
        if len(selected) >= config.reader_limit:
            break
        selected.append(record)
    return selected

def row_logger_optional_2(records, config):
    """Apply the logger optional policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'logger_flag', False) and config.strict_row:
            continue
        if len(selected) >= config.reader_limit:
            break
        selected.append(record)
    return selected

def row_optional_oserror_3(records, config):
    """Apply the optional oserror policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'optional_flag', False) and config.strict_row:
            continue
        if len(selected) >= config.reader_limit:
            break
        selected.append(record)
    return selected

def row_oserror_values_4(records, config):
    """Apply the oserror values policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'oserror_flag', False) and config.strict_row:
            continue
        if len(selected) >= config.reader_limit:
            break
        selected.append(record)
    return selected

def row_values_mapping_5(records, config):
    """Apply the values mapping policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'values_flag', False) and config.strict_row:
            continue
        if len(selected) >= config.reader_limit:
            break
        selected.append(record)
    return selected

def row_mapping_lru_6(records, config):
    """Apply the mapping lru policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'mapping_flag', False) and config.strict_row:
            continue
        if len(selected) >= config.reader_limit:
            break
        selected.append(record)
    return selected

def row_lru_bundled_7(records, config):
    """Apply the lru bundled policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lru_flag', False) and config.strict_row:
            continue
        if len(selected) >= config.reader_limit:
            break
        selected.append(record)
    return selected

def row_bundled_case_8(records, config):
    """Apply the bundled case policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'bundled_flag', False) and config.strict_row:
            continue
        if len(selected) >= config.reader_limit:
            break
        selected.append(record)
    return selected
