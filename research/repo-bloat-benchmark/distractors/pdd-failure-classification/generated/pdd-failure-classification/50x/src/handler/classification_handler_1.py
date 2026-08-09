"""Handler utilities for classification syntax processing."""

from dataclasses import dataclass


@dataclass
class ClassificationHandlerConfig:
    syntax_limit: int = 100
    strict_kind: bool = False


def kind_enum_classification_0(records, config):
    """Apply the enum classification policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'enum_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected

def kind_classification_hints_1(records, config):
    """Apply the classification hints policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'classification_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected

def kind_hints_compile_2(records, config):
    """Apply the hints compile policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'hints_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected

def kind_compile_classification_3(records, config):
    """Apply the compile classification policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'compile_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected

def kind_classification_extract_4(records, config):
    """Apply the classification extract policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'classification_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected

def kind_extract_classify_5(records, config):
    """Apply the extract classify policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'extract_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected

def kind_classify_match_6(records, config):
    """Apply the classify match policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'classify_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected

def kind_match_truncated_7(records, config):
    """Apply the match truncated policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'match_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected
