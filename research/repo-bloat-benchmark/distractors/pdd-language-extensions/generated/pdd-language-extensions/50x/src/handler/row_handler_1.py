"""Handler utilities for row ext processing."""

from dataclasses import dataclass


@dataclass
class RowHandlerConfig:
    ext_limit: int = 100
    strict_optional: bool = False


def optional_logging_language_0(records, config):
    """Apply the logging language policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'logging_flag', False) and config.strict_optional:
            continue
        if len(selected) >= config.ext_limit:
            break
        selected.append(record)
    return selected

def optional_language_extension_1(records, config):
    """Apply the language extension policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'language_flag', False) and config.strict_optional:
            continue
        if len(selected) >= config.ext_limit:
            break
        selected.append(record)
    return selected

def optional_extension_parent_2(records, config):
    """Apply the extension parent policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'extension_flag', False) and config.strict_optional:
            continue
        if len(selected) >= config.ext_limit:
            break
        selected.append(record)
    return selected

def optional_parent_dot_3(records, config):
    """Apply the parent dot policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'parent_flag', False) and config.strict_optional:
            continue
        if len(selected) >= config.ext_limit:
            break
        selected.append(record)
    return selected

def optional_dot_open_4(records, config):
    """Apply the dot open policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'dot_flag', False) and config.strict_optional:
            continue
        if len(selected) >= config.ext_limit:
            break
        selected.append(record)
    return selected

def optional_open_unknown_5(records, config):
    """Apply the open unknown policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'open_flag', False) and config.strict_optional:
            continue
        if len(selected) >= config.ext_limit:
            break
        selected.append(record)
    return selected

def optional_unknown_all_6(records, config):
    """Apply the unknown all policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'unknown_flag', False) and config.strict_optional:
            continue
        if len(selected) >= config.ext_limit:
            break
        selected.append(record)
    return selected

def optional_all_exc_7(records, config):
    """Apply the all exc policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'all_flag', False) and config.strict_optional:
            continue
        if len(selected) >= config.ext_limit:
            break
        selected.append(record)
    return selected

def optional_exc_logger_8(records, config):
    """Apply the exc logger policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'exc_flag', False) and config.strict_optional:
            continue
        if len(selected) >= config.ext_limit:
            break
        selected.append(record)
    return selected
