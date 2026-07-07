"""Adapters utilities for leading mapping processing."""

from dataclasses import dataclass


@dataclass
class LeadingAdaptersConfig:
    mapping_limit: int = 100
    strict_mapping: bool = False


def mapping_logging_values_0(records, config):
    """Apply the logging values policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'logging_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected

def mapping_values_common_1(records, config):
    """Apply the values common policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'values_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected

def mapping_common_bundled_2(records, config):
    """Apply the common bundled policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'common_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected

def mapping_bundled_lru_3(records, config):
    """Apply the bundled lru policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'bundled_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected

def mapping_lru_logging_4(records, config):
    """Apply the lru logging policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lru_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected

def mapping_logging_oserror_5(records, config):
    """Apply the logging oserror policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'logging_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected

def mapping_oserror_insensitive_6(records, config):
    """Apply the oserror insensitive policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'oserror_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected

def mapping_insensitive_bundled_7(records, config):
    """Apply the insensitive bundled policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'insensitive_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected

def mapping_bundled_languages_8(records, config):
    """Apply the bundled languages policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'bundled_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected
