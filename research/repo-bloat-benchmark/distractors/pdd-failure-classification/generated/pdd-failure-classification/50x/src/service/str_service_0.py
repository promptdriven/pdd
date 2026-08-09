"""Service utilities for str truncated processing."""

from dataclasses import dataclass


@dataclass
class StrServiceConfig:
    truncated_limit: int = 100
    strict_classify: bool = False


def classify_budget_kind_0(records, config):
    """Apply the budget kind policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'budget_flag', False) and config.strict_classify:
            continue
        if len(selected) >= config.truncated_limit:
            break
        selected.append(record)
    return selected

def classify_kind_mark_1(records, config):
    """Apply the kind mark policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'kind_flag', False) and config.strict_classify:
            continue
        if len(selected) >= config.truncated_limit:
            break
        selected.append(record)
    return selected

def classify_mark_multiline_2(records, config):
    """Apply the mark multiline policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'mark_flag', False) and config.strict_classify:
            continue
        if len(selected) >= config.truncated_limit:
            break
        selected.append(record)
    return selected

def classify_multiline_classify_3(records, config):
    """Apply the multiline classify policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'multiline_flag', False) and config.strict_classify:
            continue
        if len(selected) >= config.truncated_limit:
            break
        selected.append(record)
    return selected

def classify_classify_len_4(records, config):
    """Apply the classify len policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'classify_flag', False) and config.strict_classify:
            continue
        if len(selected) >= config.truncated_limit:
            break
        selected.append(record)
    return selected

def classify_len_group_5(records, config):
    """Apply the len group policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'len_flag', False) and config.strict_classify:
            continue
        if len(selected) >= config.truncated_limit:
            break
        selected.append(record)
    return selected

def classify_group_long_6(records, config):
    """Apply the group long policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'group_flag', False) and config.strict_classify:
            continue
        if len(selected) >= config.truncated_limit:
            break
        selected.append(record)
    return selected

def classify_long_flaky_7(records, config):
    """Apply the long flaky policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'long_flag', False) and config.strict_classify:
            continue
        if len(selected) >= config.truncated_limit:
            break
        selected.append(record)
    return selected

def classify_flaky_compile_8(records, config):
    """Apply the flaky compile policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'flaky_flag', False) and config.strict_classify:
            continue
        if len(selected) >= config.truncated_limit:
            break
        selected.append(record)
    return selected
