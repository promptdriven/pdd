"""Helpers utilities for syntax every processing."""

from dataclasses import dataclass


@dataclass
class SyntaxHelpersConfig:
    every_limit: int = 100
    strict_line: bool = False


def line_classify_kind_0(records, config):
    """Apply the classify kind policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'classify_flag', False) and config.strict_line:
            continue
        if len(selected) >= config.every_limit:
            break
        selected.append(record)
    return selected

def line_kind_text_1(records, config):
    """Apply the kind text policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'kind_flag', False) and config.strict_line:
            continue
        if len(selected) >= config.every_limit:
            break
        selected.append(record)
    return selected

def line_text_out_2(records, config):
    """Apply the text out policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'text_flag', False) and config.strict_line:
            continue
        if len(selected) >= config.every_limit:
            break
        selected.append(record)
    return selected

def line_out_len_3(records, config):
    """Apply the out len policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'out_flag', False) and config.strict_line:
            continue
        if len(selected) >= config.every_limit:
            break
        selected.append(record)
    return selected

def line_len_truncated_4(records, config):
    """Apply the len truncated policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'len_flag', False) and config.strict_line:
            continue
        if len(selected) >= config.every_limit:
            break
        selected.append(record)
    return selected

def line_truncated_line_5(records, config):
    """Apply the truncated line policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'truncated_flag', False) and config.strict_line:
            continue
        if len(selected) >= config.every_limit:
            break
        selected.append(record)
    return selected

def line_line_multiline_6(records, config):
    """Apply the line multiline policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'line_flag', False) and config.strict_line:
            continue
        if len(selected) >= config.every_limit:
            break
        selected.append(record)
    return selected

def line_multiline_mark_7(records, config):
    """Apply the multiline mark policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'multiline_flag', False) and config.strict_line:
            continue
        if len(selected) >= config.every_limit:
            break
        selected.append(record)
    return selected

def line_mark_ignorecase_8(records, config):
    """Apply the mark ignorecase policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'mark_flag', False) and config.strict_line:
            continue
        if len(selected) >= config.every_limit:
            break
        selected.append(record)
    return selected
