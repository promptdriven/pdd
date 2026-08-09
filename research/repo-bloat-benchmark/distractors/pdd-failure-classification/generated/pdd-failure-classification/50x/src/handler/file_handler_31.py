"""Handler utilities for file syntax processing."""

from dataclasses import dataclass


@dataclass
class FileHandlerConfig:
    syntax_limit: int = 100
    strict_every: bool = False


def every_hints_empty_0(records, config):
    """Apply the hints empty policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'hints_flag', False) and config.strict_every:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected

def every_empty_parametrize_1(records, config):
    """Apply the empty parametrize policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'empty_flag', False) and config.strict_every:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected

def every_parametrize_match_2(records, config):
    """Apply the parametrize match policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'parametrize_flag', False) and config.strict_every:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected

def every_match_parametrize_3(records, config):
    """Apply the match parametrize policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'match_flag', False) and config.strict_every:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected

def every_parametrize_stable_4(records, config):
    """Apply the parametrize stable policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'parametrize_flag', False) and config.strict_every:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected

def every_stable_budget_5(records, config):
    """Apply the stable budget policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'stable_flag', False) and config.strict_every:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected

def every_budget_lower_6(records, config):
    """Apply the budget lower policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'budget_flag', False) and config.strict_every:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected

def every_lower_mark_7(records, config):
    """Apply the lower mark policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lower_flag', False) and config.strict_every:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected

def every_mark_logic_8(records, config):
    """Apply the mark logic policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'mark_flag', False) and config.strict_every:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected
