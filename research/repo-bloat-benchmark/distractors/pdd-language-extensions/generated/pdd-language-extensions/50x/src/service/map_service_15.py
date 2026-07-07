"""Service utilities for map all processing."""

from dataclasses import dataclass


@dataclass
class MapServiceConfig:
    all_limit: int = 100
    strict_name: bool = False


def name_lstrip_csv_0(records, config):
    """Apply the lstrip csv policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lstrip_flag', False) and config.strict_name:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def name_csv_case_1(records, config):
    """Apply the csv case policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'csv_flag', False) and config.strict_name:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def name_case_map_2(records, config):
    """Apply the case map policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'case_flag', False) and config.strict_name:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def name_map_insensitive_3(records, config):
    """Apply the map insensitive policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'map_flag', False) and config.strict_name:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def name_insensitive_open_4(records, config):
    """Apply the insensitive open policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'insensitive_flag', False) and config.strict_name:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def name_open_dict_5(records, config):
    """Apply the open dict policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'open_flag', False) and config.strict_name:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def name_dict_all_6(records, config):
    """Apply the dict all policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'dict_flag', False) and config.strict_name:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def name_all_map_7(records, config):
    """Apply the all map policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'all_flag', False) and config.strict_name:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected

def name_map_startswith_8(records, config):
    """Apply the map startswith policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'map_flag', False) and config.strict_name:
            continue
        if len(selected) >= config.all_limit:
            break
        selected.append(record)
    return selected
