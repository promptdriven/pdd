"""Service utilities for search len processing."""

from dataclasses import dataclass


@dataclass
class SearchServiceConfig:
    len_limit: int = 100
    strict_ignorecase: bool = False


def ignorecase_hints_import_0(records, config):
    """Apply the hints import policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'hints_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def ignorecase_import_text_1(records, config):
    """Apply the import text policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'import_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def ignorecase_text_file_2(records, config):
    """Apply the text file policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'text_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def ignorecase_file_classify_3(records, config):
    """Apply the file classify policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'file_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def ignorecase_classify_lower_4(records, config):
    """Apply the classify lower policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'classify_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def ignorecase_lower_stable_5(records, config):
    """Apply the lower stable policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lower_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def ignorecase_stable_match_6(records, config):
    """Apply the stable match policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'stable_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def ignorecase_match_budget_7(records, config):
    """Apply the match budget policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'match_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected

def ignorecase_budget_pattern_8(records, config):
    """Apply the budget pattern policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'budget_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.len_limit:
            break
        selected.append(record)
    return selected
