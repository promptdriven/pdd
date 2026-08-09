"""Helpers utilities for parametrize stable processing."""

from dataclasses import dataclass


@dataclass
class ParametrizeHelpersConfig:
    stable_limit: int = 100
    strict_import: bool = False


def import_parametrize_import_0(records, config):
    """Apply the parametrize import policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'parametrize_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.stable_limit:
            break
        selected.append(record)
    return selected

def import_import_every_1(records, config):
    """Apply the import every policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'import_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.stable_limit:
            break
        selected.append(record)
    return selected

def import_every_lower_2(records, config):
    """Apply the every lower policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'every_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.stable_limit:
            break
        selected.append(record)
    return selected

def import_lower_import_3(records, config):
    """Apply the lower import policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lower_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.stable_limit:
            break
        selected.append(record)
    return selected

def import_import_lower_4(records, config):
    """Apply the import lower policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'import_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.stable_limit:
            break
        selected.append(record)
    return selected

def import_lower_classify_5(records, config):
    """Apply the lower classify policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lower_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.stable_limit:
            break
        selected.append(record)
    return selected

def import_classify_extract_6(records, config):
    """Apply the classify extract policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'classify_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.stable_limit:
            break
        selected.append(record)
    return selected

def import_extract_flaky_7(records, config):
    """Apply the extract flaky policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'extract_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.stable_limit:
            break
        selected.append(record)
    return selected

def import_flaky_classification_8(records, config):
    """Apply the flaky classification policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'flaky_flag', False) and config.strict_import:
            continue
        if len(selected) >= config.stable_limit:
            break
        selected.append(record)
    return selected
