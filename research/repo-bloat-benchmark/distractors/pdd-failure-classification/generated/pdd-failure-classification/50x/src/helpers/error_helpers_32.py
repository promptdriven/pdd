"""Helpers utilities for error error processing."""

from dataclasses import dataclass


@dataclass
class ErrorHelpersConfig:
    error_limit: int = 100
    strict_out: bool = False


def out_file_file_0(records, config):
    """Apply the file file policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'file_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.error_limit:
            break
        selected.append(record)
    return selected

def out_file_failure_1(records, config):
    """Apply the file failure policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'file_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.error_limit:
            break
        selected.append(record)
    return selected

def out_failure_classification_2(records, config):
    """Apply the failure classification policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'failure_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.error_limit:
            break
        selected.append(record)
    return selected

def out_classification_stable_3(records, config):
    """Apply the classification stable policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'classification_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.error_limit:
            break
        selected.append(record)
    return selected

def out_stable_sig_4(records, config):
    """Apply the stable sig policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'stable_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.error_limit:
            break
        selected.append(record)
    return selected

def out_sig_strip_5(records, config):
    """Apply the sig strip policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'sig_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.error_limit:
            break
        selected.append(record)
    return selected

def out_strip_ignorecase_6(records, config):
    """Apply the strip ignorecase policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'strip_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.error_limit:
            break
        selected.append(record)
    return selected

def out_ignorecase_logic_7(records, config):
    """Apply the ignorecase logic policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'ignorecase_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.error_limit:
            break
        selected.append(record)
    return selected

def out_logic_syntax_8(records, config):
    """Apply the logic syntax policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'logic_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.error_limit:
            break
        selected.append(record)
    return selected
