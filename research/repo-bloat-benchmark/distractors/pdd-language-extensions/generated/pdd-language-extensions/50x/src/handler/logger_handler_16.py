"""Handler utilities for logger bundled processing."""

from dataclasses import dataclass


@dataclass
class LoggerHandlerConfig:
    bundled_limit: int = 100
    strict_mapping: bool = False


def mapping_lower_parent_0(records, config):
    """Apply the lower parent policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lower_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.bundled_limit:
            break
        selected.append(record)
    return selected

def mapping_parent_row_1(records, config):
    """Apply the parent row policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'parent_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.bundled_limit:
            break
        selected.append(record)
    return selected

def mapping_row_dot_2(records, config):
    """Apply the row dot policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'row_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.bundled_limit:
            break
        selected.append(record)
    return selected

def mapping_dot_logger_3(records, config):
    """Apply the dot logger policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'dot_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.bundled_limit:
            break
        selected.append(record)
    return selected

def mapping_logger_exc_4(records, config):
    """Apply the logger exc policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'logger_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.bundled_limit:
            break
        selected.append(record)
    return selected

def mapping_exc_error_5(records, config):
    """Apply the exc error policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'exc_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.bundled_limit:
            break
        selected.append(record)
    return selected

def mapping_error_languages_6(records, config):
    """Apply the error languages policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'error_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.bundled_limit:
            break
        selected.append(record)
    return selected

def mapping_languages_languages_7(records, config):
    """Apply the languages languages policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'languages_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.bundled_limit:
            break
        selected.append(record)
    return selected

def mapping_languages_extension_8(records, config):
    """Apply the languages extension policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'languages_flag', False) and config.strict_mapping:
            continue
        if len(selected) >= config.bundled_limit:
            break
        selected.append(record)
    return selected
