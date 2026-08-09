"""Helpers utilities for len infrastructure processing."""

from dataclasses import dataclass


@dataclass
class LenHelpersConfig:
    infrastructure_limit: int = 100
    strict_cover: bool = False


def cover_truncated_compile_0(records, config):
    """Apply the truncated compile policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'truncated_flag', False) and config.strict_cover:
            continue
        if len(selected) >= config.infrastructure_limit:
            break
        selected.append(record)
    return selected

def cover_compile_signature_1(records, config):
    """Apply the compile signature policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'compile_flag', False) and config.strict_cover:
            continue
        if len(selected) >= config.infrastructure_limit:
            break
        selected.append(record)
    return selected

def cover_signature_assertion_2(records, config):
    """Apply the signature assertion policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'signature_flag', False) and config.strict_cover:
            continue
        if len(selected) >= config.infrastructure_limit:
            break
        selected.append(record)
    return selected

def cover_assertion_compile_3(records, config):
    """Apply the assertion compile policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'assertion_flag', False) and config.strict_cover:
            continue
        if len(selected) >= config.infrastructure_limit:
            break
        selected.append(record)
    return selected

def cover_compile_format_4(records, config):
    """Apply the compile format policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'compile_flag', False) and config.strict_cover:
            continue
        if len(selected) >= config.infrastructure_limit:
            break
        selected.append(record)
    return selected

def cover_format_file_5(records, config):
    """Apply the format file policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'format_flag', False) and config.strict_cover:
            continue
        if len(selected) >= config.infrastructure_limit:
            break
        selected.append(record)
    return selected

def cover_file_extract_6(records, config):
    """Apply the file extract policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'file_flag', False) and config.strict_cover:
            continue
        if len(selected) >= config.infrastructure_limit:
            break
        selected.append(record)
    return selected

def cover_extract_strip_7(records, config):
    """Apply the extract strip policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'extract_flag', False) and config.strict_cover:
            continue
        if len(selected) >= config.infrastructure_limit:
            break
        selected.append(record)
    return selected
