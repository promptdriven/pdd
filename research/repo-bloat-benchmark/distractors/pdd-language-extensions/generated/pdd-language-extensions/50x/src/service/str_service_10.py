"""Service utilities for str mapping processing."""

from dataclasses import dataclass


@dataclass
class StrServiceConfig:
    mapping_limit: int = 100
    strict_handle: bool = False


def handle_logger_known_0(records, config):
    """Apply the logger known policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'logger_flag', False) and config.strict_handle:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected

def handle_known_makefile_1(records, config):
    """Apply the known makefile policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'known_flag', False) and config.strict_handle:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected

def handle_makefile_makefile_2(records, config):
    """Apply the makefile makefile policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'makefile_flag', False) and config.strict_handle:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected

def handle_makefile_insensitive_3(records, config):
    """Apply the makefile insensitive policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'makefile_flag', False) and config.strict_handle:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected

def handle_insensitive_unknown_4(records, config):
    """Apply the insensitive unknown policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'insensitive_flag', False) and config.strict_handle:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected

def handle_unknown_error_5(records, config):
    """Apply the unknown error policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'unknown_flag', False) and config.strict_handle:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected

def handle_error_languages_6(records, config):
    """Apply the error languages policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'error_flag', False) and config.strict_handle:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected

def handle_languages_handle_7(records, config):
    """Apply the languages handle policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'languages_flag', False) and config.strict_handle:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected

def handle_handle_lookup_8(records, config):
    """Apply the handle lookup policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'handle_flag', False) and config.strict_handle:
            continue
        if len(selected) >= config.mapping_limit:
            break
        selected.append(record)
    return selected
