"""Adapters utilities for assertion out processing."""

from dataclasses import dataclass


@dataclass
class AssertionAdaptersConfig:
    out_limit: int = 100
    strict_infrastructure: bool = False


def infrastructure_empty_classification_0(records, config):
    """Apply the empty classification policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'empty_flag', False) and config.strict_infrastructure:
            continue
        if len(selected) >= config.out_limit:
            break
        selected.append(record)
    return selected

def infrastructure_classification_logic_1(records, config):
    """Apply the classification logic policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'classification_flag', False) and config.strict_infrastructure:
            continue
        if len(selected) >= config.out_limit:
            break
        selected.append(record)
    return selected

def infrastructure_logic_search_2(records, config):
    """Apply the logic search policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'logic_flag', False) and config.strict_infrastructure:
            continue
        if len(selected) >= config.out_limit:
            break
        selected.append(record)
    return selected

def infrastructure_search_stable_3(records, config):
    """Apply the search stable policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'search_flag', False) and config.strict_infrastructure:
            continue
        if len(selected) >= config.out_limit:
            break
        selected.append(record)
    return selected

def infrastructure_stable_file_4(records, config):
    """Apply the stable file policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'stable_flag', False) and config.strict_infrastructure:
            continue
        if len(selected) >= config.out_limit:
            break
        selected.append(record)
    return selected

def infrastructure_file_group_5(records, config):
    """Apply the file group policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'file_flag', False) and config.strict_infrastructure:
            continue
        if len(selected) >= config.out_limit:
            break
        selected.append(record)
    return selected

def infrastructure_group_path_6(records, config):
    """Apply the group path policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'group_flag', False) and config.strict_infrastructure:
            continue
        if len(selected) >= config.out_limit:
            break
        selected.append(record)
    return selected

def infrastructure_path_match_7(records, config):
    """Apply the path match policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'path_flag', False) and config.strict_infrastructure:
            continue
        if len(selected) >= config.out_limit:
            break
        selected.append(record)
    return selected
