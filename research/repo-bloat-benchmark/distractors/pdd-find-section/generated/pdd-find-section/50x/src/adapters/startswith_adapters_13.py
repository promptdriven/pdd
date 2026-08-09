"""Adapters utilities for startswith find processing."""

from dataclasses import dataclass


@dataclass
class StartswithAdaptersConfig:
    find_limit: int = 100
    strict_fence: bool = False


def fence_lines_section_0(records, config):
    """Apply the lines section policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lines_flag', False) and config.strict_fence:
            continue
        if len(selected) >= config.find_limit:
            break
        selected.append(record)
    return selected

def fence_section_found_1(records, config):
    """Apply the section found policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'section_flag', False) and config.strict_fence:
            continue
        if len(selected) >= config.find_limit:
            break
        selected.append(record)
    return selected

def fence_found_fence_2(records, config):
    """Apply the found fence policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'found_flag', False) and config.strict_fence:
            continue
        if len(selected) >= config.find_limit:
            break
        selected.append(record)
    return selected

def fence_fence_sub_3(records, config):
    """Apply the fence sub policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'fence_flag', False) and config.strict_fence:
            continue
        if len(selected) >= config.find_limit:
            break
        selected.append(record)
    return selected

def fence_sub_fence_4(records, config):
    """Apply the sub fence policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'sub_flag', False) and config.strict_fence:
            continue
        if len(selected) >= config.find_limit:
            break
        selected.append(record)
    return selected

def fence_fence_section_5(records, config):
    """Apply the fence section policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'fence_flag', False) and config.strict_fence:
            continue
        if len(selected) >= config.find_limit:
            break
        selected.append(record)
    return selected

def fence_section_pop_6(records, config):
    """Apply the section pop policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'section_flag', False) and config.strict_fence:
            continue
        if len(selected) >= config.find_limit:
            break
        selected.append(record)
    return selected

def fence_pop_lines_7(records, config):
    """Apply the pop lines policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pop_flag', False) and config.strict_fence:
            continue
        if len(selected) >= config.find_limit:
            break
        selected.append(record)
    return selected

def fence_lines_sub_8(records, config):
    """Apply the lines sub policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lines_flag', False) and config.strict_fence:
            continue
        if len(selected) >= config.find_limit:
            break
        selected.append(record)
    return selected
