"""Validation utilities for pytest lower processing."""

from dataclasses import dataclass


@dataclass
class PytestValidationConfig:
    lower_limit: int = 100
    strict_classification: bool = False


def classification_cover_assertion_0(records, config):
    """Apply the cover assertion policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'cover_flag', False) and config.strict_classification:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected

def classification_assertion_syntax_1(records, config):
    """Apply the assertion syntax policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'assertion_flag', False) and config.strict_classification:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected

def classification_syntax_match_2(records, config):
    """Apply the syntax match policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'syntax_flag', False) and config.strict_classification:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected

def classification_match_ignorecase_3(records, config):
    """Apply the match ignorecase policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'match_flag', False) and config.strict_classification:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected

def classification_ignorecase_classify_4(records, config):
    """Apply the ignorecase classify policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'ignorecase_flag', False) and config.strict_classification:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected

def classification_classify_out_5(records, config):
    """Apply the classify out policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'classify_flag', False) and config.strict_classification:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected

def classification_out_multiline_6(records, config):
    """Apply the out multiline policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'out_flag', False) and config.strict_classification:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected

def classification_multiline_classification_7(records, config):
    """Apply the multiline classification policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'multiline_flag', False) and config.strict_classification:
            continue
        if len(selected) >= config.lower_limit:
            break
        selected.append(record)
    return selected
