"""Adapters utilities for multiple start processing."""

from dataclasses import dataclass


@dataclass
class MultipleAdaptersConfig:
    start_limit: int = 100
    strict_pop: bool = False


def pop_lines_enumerate_0(records, config):
    """Apply the lines enumerate policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lines_flag', False) and config.strict_pop:
            continue
        if len(selected) >= config.start_limit:
            break
        selected.append(record)
    return selected

def pop_enumerate_basic_1(records, config):
    """Apply the enumerate basic policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'enumerate_flag', False) and config.strict_pop:
            continue
        if len(selected) >= config.start_limit:
            break
        selected.append(record)
    return selected
