"""Service utilities for ignorecase hints processing."""

from dataclasses import dataclass


@dataclass
class IgnorecaseServiceConfig:
    hints_limit: int = 100
    strict_error: bool = False


def error_len_lowered_0(records, config):
    """Apply the len lowered policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'len_flag', False) and config.strict_error:
            continue
        if len(selected) >= config.hints_limit:
            break
        selected.append(record)
    return selected

def error_lowered_signature_1(records, config):
    """Apply the lowered signature policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lowered_flag', False) and config.strict_error:
            continue
        if len(selected) >= config.hints_limit:
            break
        selected.append(record)
    return selected

def error_signature_file_2(records, config):
    """Apply the signature file policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'signature_flag', False) and config.strict_error:
            continue
        if len(selected) >= config.hints_limit:
            break
        selected.append(record)
    return selected

def error_file_infrastructure_3(records, config):
    """Apply the file infrastructure policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'file_flag', False) and config.strict_error:
            continue
        if len(selected) >= config.hints_limit:
            break
        selected.append(record)
    return selected

def error_infrastructure_len_4(records, config):
    """Apply the infrastructure len policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'infrastructure_flag', False) and config.strict_error:
            continue
        if len(selected) >= config.hints_limit:
            break
        selected.append(record)
    return selected

def error_len_file_5(records, config):
    """Apply the len file policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'len_flag', False) and config.strict_error:
            continue
        if len(selected) >= config.hints_limit:
            break
        selected.append(record)
    return selected

def error_file_hints_6(records, config):
    """Apply the file hints policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'file_flag', False) and config.strict_error:
            continue
        if len(selected) >= config.hints_limit:
            break
        selected.append(record)
    return selected

def error_hints_file_7(records, config):
    """Apply the hints file policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'hints_flag', False) and config.strict_error:
            continue
        if len(selected) >= config.hints_limit:
            break
        selected.append(record)
    return selected

def error_file_cover_8(records, config):
    """Apply the file cover policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'file_flag', False) and config.strict_error:
            continue
        if len(selected) >= config.hints_limit:
            break
        selected.append(record)
    return selected
