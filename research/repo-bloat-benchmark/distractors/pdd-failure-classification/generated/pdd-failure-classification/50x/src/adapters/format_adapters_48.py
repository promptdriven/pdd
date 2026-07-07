"""Adapters utilities for format len processing."""

from dataclasses import dataclass


@dataclass
class FormatAdaptersConfig:
    len_limit: int = 100
    strict_parametrize: bool = False


def parametrize_len_hint_0(records, config):
    """Apply the len hint policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'len_flag', False) and config.strict_parametrize:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def parametrize_hint_strip_1(records, config):
    """Apply the hint strip policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'hint_flag', False) and config.strict_parametrize:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def parametrize_strip_lowered_2(records, config):
    """Apply the strip lowered policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'strip_flag', False) and config.strict_parametrize:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def parametrize_lowered_syntax_3(records, config):
    """Apply the lowered syntax policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lowered_flag', False) and config.strict_parametrize:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def parametrize_syntax_file_4(records, config):
    """Apply the syntax file policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'syntax_flag', False) and config.strict_parametrize:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def parametrize_file_classify_5(records, config):
    """Apply the file classify policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'file_flag', False) and config.strict_parametrize:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def parametrize_classify_syntax_6(records, config):
    """Apply the classify syntax policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'classify_flag', False) and config.strict_parametrize:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def parametrize_syntax_extract_7(records, config):
    """Apply the syntax extract policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'syntax_flag', False) and config.strict_parametrize:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def parametrize_extract_truncated_8(records, config):
    """Apply the extract truncated policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'extract_flag', False) and config.strict_parametrize:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected
