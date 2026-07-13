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
