"""Service utilities for infrastructure logic processing."""

from dataclasses import dataclass


@dataclass
class InfrastructureServiceConfig:
    logic_limit: int = 100
    strict_kind: bool = False


def kind_out_failure_0(records, config):
    """Apply the out failure policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'out_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.logic_limit:
            break
        selected.append(record)
    return selected

def kind_failure_path_1(records, config):
    """Apply the failure path policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'failure_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.logic_limit:
            break
        selected.append(record)
    return selected

def kind_path_lowered_2(records, config):
    """Apply the path lowered policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'path_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.logic_limit:
            break
        selected.append(record)
    return selected

def kind_lowered_compile_3(records, config):
    """Apply the lowered compile policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lowered_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.logic_limit:
            break
        selected.append(record)
    return selected

def kind_compile_str_4(records, config):
    """Apply the compile str policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'compile_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.logic_limit:
            break
        selected.append(record)
    return selected

def kind_str_kind_5(records, config):
    """Apply the str kind policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'str_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.logic_limit:
            break
        selected.append(record)
    return selected

def kind_kind_pytest_6(records, config):
    """Apply the kind pytest policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'kind_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.logic_limit:
            break
        selected.append(record)
    return selected

def kind_pytest_every_7(records, config):
    """Apply the pytest every policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pytest_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.logic_limit:
            break
        selected.append(record)
    return selected

def kind_every_lower_8(records, config):
    """Apply the every lower policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'every_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.logic_limit:
            break
        selected.append(record)
    return selected
