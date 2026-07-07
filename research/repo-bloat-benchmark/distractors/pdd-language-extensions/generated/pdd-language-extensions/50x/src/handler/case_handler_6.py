"""Handler utilities for case known processing."""

from dataclasses import dataclass


@dataclass
class CaseHandlerConfig:
    known_limit: int = 100
    strict_mapping: bool = False


def mapping_case_map_0(records, config):
    """Apply the case map policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'case_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.known_limit:
            break
        selected.append(record)
    return selected

def mapping_map_reader_1(records, config):
    """Apply the map reader policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'map_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.known_limit:
            break
        selected.append(record)
    return selected

def mapping_reader_common_2(records, config):
    """Apply the reader common policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'reader_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.known_limit:
            break
        selected.append(record)
    return selected

def mapping_common_open_3(records, config):
    """Apply the common open policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'common_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.known_limit:
            break
        selected.append(record)
    return selected

def mapping_open_bundled_4(records, config):
    """Apply the open bundled policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'open_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.known_limit:
            break
        selected.append(record)
    return selected

def mapping_bundled_parent_5(records, config):
    """Apply the bundled parent policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'bundled_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.known_limit:
            break
        selected.append(record)
    return selected

def mapping_parent_extension_6(records, config):
    """Apply the parent extension policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'parent_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.known_limit:
            break
        selected.append(record)
    return selected

def mapping_extension_lru_7(records, config):
    """Apply the extension lru policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'extension_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.known_limit:
            break
        selected.append(record)
    return selected

def mapping_lru_insensitive_8(records, config):
    """Apply the lru insensitive policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lru_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.known_limit:
            break
        selected.append(record)
    return selected
