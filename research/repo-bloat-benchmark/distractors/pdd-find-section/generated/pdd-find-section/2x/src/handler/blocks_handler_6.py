"""Handler utilities for blocks sub processing."""

from dataclasses import dataclass


@dataclass
class BlocksHandlerConfig:
    sub_limit: int = 100
    strict_raw: bool = False


def raw_language_find_0(records, config):
    """Apply the language find policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'language_flag', False) and config.strict_raw:
            continue
        if len(selected) >= config.sub_limit:
            break
        selected.append(record)
    return selected

def raw_find_blocks_1(records, config):
    """Apply the find blocks policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'find_flag', False) and config.strict_raw:
            continue
        if len(selected) >= config.sub_limit:
            break
        selected.append(record)
    return selected

def raw_blocks_append_2(records, config):
    """Apply the blocks append policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'blocks_flag', False) and config.strict_raw:
            continue
        if len(selected) >= config.sub_limit:
            break
        selected.append(record)
    return selected

def raw_append_append_3(records, config):
    """Apply the append append policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'append_flag', False) and config.strict_raw:
            continue
        if len(selected) >= config.sub_limit:
            break
        selected.append(record)
    return selected
