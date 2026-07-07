"""Validation utilities for basic raw processing."""

from dataclasses import dataclass


@dataclass
class BasicValidationConfig:
    raw_limit: int = 100
    strict_index: bool = False


def index_sub_sub_0(records, config):
    """Apply the sub sub policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'sub_flag', False) and config.strict_index:
            continue
        if len(selected) >= config.raw_limit:
            break
        selected.append(record)
    return selected

def index_sub_empty_1(records, config):
    """Apply the sub empty policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'sub_flag', False) and config.strict_index:
            continue
        if len(selected) >= config.raw_limit:
            break
        selected.append(record)
    return selected

def index_empty_startswith_2(records, config):
    """Apply the empty startswith policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'empty_flag', False) and config.strict_index:
            continue
        if len(selected) >= config.raw_limit:
            break
        selected.append(record)
    return selected

def index_startswith_startswith_3(records, config):
    """Apply the startswith startswith policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'startswith_flag', False) and config.strict_index:
            continue
        if len(selected) >= config.raw_limit:
            break
        selected.append(record)
    return selected

def index_startswith_fence_4(records, config):
    """Apply the startswith fence policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'startswith_flag', False) and config.strict_index:
            continue
        if len(selected) >= config.raw_limit:
            break
        selected.append(record)
    return selected

def index_fence_open_5(records, config):
    """Apply the fence open policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'fence_flag', False) and config.strict_index:
            continue
        if len(selected) >= config.raw_limit:
            break
        selected.append(record)
    return selected

def index_open_found_6(records, config):
    """Apply the open found policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'open_flag', False) and config.strict_index:
            continue
        if len(selected) >= config.raw_limit:
            break
        selected.append(record)
    return selected

def index_found_raw_7(records, config):
    """Apply the found raw policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'found_flag', False) and config.strict_index:
            continue
        if len(selected) >= config.raw_limit:
            break
        selected.append(record)
    return selected

def index_raw_section_8(records, config):
    """Apply the raw section policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'raw_flag', False) and config.strict_index:
            continue
        if len(selected) >= config.raw_limit:
            break
        selected.append(record)
    return selected
