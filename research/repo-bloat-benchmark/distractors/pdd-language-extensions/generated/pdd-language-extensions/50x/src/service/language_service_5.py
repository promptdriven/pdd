"""Service utilities for language language processing."""

from dataclasses import dataclass


@dataclass
class LanguageServiceConfig:
    language_limit: int = 100
    strict_lstrip: bool = False


def lstrip_lower_logger_0(records, config):
    """Apply the lower logger policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lower_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.language_limit:
            break
        selected.append(record)
    return selected

def lstrip_logger_known_1(records, config):
    """Apply the logger known policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'logger_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.language_limit:
            break
        selected.append(record)
    return selected

def lstrip_known_str_2(records, config):
    """Apply the known str policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'known_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.language_limit:
            break
        selected.append(record)
    return selected

def lstrip_str_mapping_3(records, config):
    """Apply the str mapping policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'str_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.language_limit:
            break
        selected.append(record)
    return selected

def lstrip_mapping_row_4(records, config):
    """Apply the mapping row policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'mapping_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.language_limit:
            break
        selected.append(record)
    return selected

def lstrip_row_handle_5(records, config):
    """Apply the row handle policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'row_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.language_limit:
            break
        selected.append(record)
    return selected

def lstrip_handle_lru_6(records, config):
    """Apply the handle lru policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'handle_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.language_limit:
            break
        selected.append(record)
    return selected

def lstrip_lru_values_7(records, config):
    """Apply the lru values policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lru_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.language_limit:
            break
        selected.append(record)
    return selected

def lstrip_values_unknown_8(records, config):
    """Apply the values unknown policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'values_flag', False) and config.strict_lstrip:
            continue
        if len(selected) >= config.language_limit:
            break
        selected.append(record)
    return selected
