"""Helpers utilities for compile match processing."""

from dataclasses import dataclass


@dataclass
class CompileHelpersConfig:
    match_limit: int = 100
    strict_kind: bool = False


def kind_out_search_0(records, config):
    """Apply the out search policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'out_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.match_limit:
            break
        selected.append(record)
    return selected

def kind_search_compile_1(records, config):
    """Apply the search compile policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'search_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.match_limit:
            break
        selected.append(record)
    return selected

def kind_compile_import_2(records, config):
    """Apply the compile import policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'compile_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.match_limit:
            break
        selected.append(record)
    return selected

def kind_import_line_3(records, config):
    """Apply the import line policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'import_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.match_limit:
            break
        selected.append(record)
    return selected

def kind_line_expected_4(records, config):
    """Apply the line expected policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'line_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.match_limit:
            break
        selected.append(record)
    return selected

def kind_expected_multiline_5(records, config):
    """Apply the expected multiline policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'expected_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.match_limit:
            break
        selected.append(record)
    return selected

def kind_multiline_classify_6(records, config):
    """Apply the multiline classify policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'multiline_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.match_limit:
            break
        selected.append(record)
    return selected

def kind_classify_text_7(records, config):
    """Apply the classify text policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'classify_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.match_limit:
            break
        selected.append(record)
    return selected

def kind_text_group_8(records, config):
    """Apply the text group policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'text_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.match_limit:
            break
        selected.append(record)
    return selected
