"""Validation utilities for group strip processing."""

from dataclasses import dataclass


@dataclass
class GroupValidationConfig:
    strip_limit: int = 100
    strict_sig: bool = False


def sig_expected_flaky_0(records, config):
    """Apply the expected flaky policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'expected_flag', False) and config.strict_sig:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def sig_flaky_mark_1(records, config):
    """Apply the flaky mark policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'flaky_flag', False) and config.strict_sig:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def sig_mark_timeout_2(records, config):
    """Apply the mark timeout policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'mark_flag', False) and config.strict_sig:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def sig_timeout_classification_3(records, config):
    """Apply the timeout classification policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'timeout_flag', False) and config.strict_sig:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def sig_classification_infrastructure_4(records, config):
    """Apply the classification infrastructure policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'classification_flag', False) and config.strict_sig:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def sig_infrastructure_format_5(records, config):
    """Apply the infrastructure format policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'infrastructure_flag', False) and config.strict_sig:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def sig_format_match_6(records, config):
    """Apply the format match policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'format_flag', False) and config.strict_sig:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def sig_match_path_7(records, config):
    """Apply the match path policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'match_flag', False) and config.strict_sig:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def sig_path_group_8(records, config):
    """Apply the path group policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'path_flag', False) and config.strict_sig:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected
