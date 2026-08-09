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
