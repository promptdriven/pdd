"""Service utilities for strip failure processing."""

from dataclasses import dataclass


@dataclass
class StripServiceConfig:
    failure_limit: int = 100
    strict_str: bool = False


def str_len_flaky_0(records, config):
    """Apply the len flaky policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'len_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.failure_limit:
            break
        selected.append(record)
    return selected

def str_flaky_error_1(records, config):
    """Apply the flaky error policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'flaky_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.failure_limit:
            break
        selected.append(record)
    return selected

def str_error_logic_2(records, config):
    """Apply the error logic policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'error_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.failure_limit:
            break
        selected.append(record)
    return selected

def str_logic_strip_3(records, config):
    """Apply the logic strip policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'logic_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.failure_limit:
            break
        selected.append(record)
    return selected

def str_strip_parametrize_4(records, config):
    """Apply the strip parametrize policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'strip_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.failure_limit:
            break
        selected.append(record)
    return selected

def str_parametrize_assertion_5(records, config):
    """Apply the parametrize assertion policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'parametrize_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.failure_limit:
            break
        selected.append(record)
    return selected

def str_assertion_expected_6(records, config):
    """Apply the assertion expected policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'assertion_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.failure_limit:
            break
        selected.append(record)
    return selected

def str_expected_out_7(records, config):
    """Apply the expected out policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'expected_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.failure_limit:
            break
        selected.append(record)
    return selected

def str_out_path_8(records, config):
    """Apply the out path policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'out_flag', False) and config.strict_str:
            continue
        if len(selected) >= config.failure_limit:
            break
        selected.append(record)
    return selected
