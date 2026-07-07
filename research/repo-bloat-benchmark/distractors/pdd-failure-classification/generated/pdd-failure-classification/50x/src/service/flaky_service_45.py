"""Service utilities for flaky ignorecase processing."""

from dataclasses import dataclass


@dataclass
class FlakyServiceConfig:
    ignorecase_limit: int = 100
    strict_enum: bool = False


def enum_exception_long_0(records, config):
    """Apply the exception long policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'exception_flag', False) and config.strict_enum:
            continue
        if len(selected) >= config.ignorecase_limit:
            break
        selected.append(record)
    return selected

def enum_long_truncated_1(records, config):
    """Apply the long truncated policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'long_flag', False) and config.strict_enum:
            continue
        if len(selected) >= config.ignorecase_limit:
            break
        selected.append(record)
    return selected

def enum_truncated_pattern_2(records, config):
    """Apply the truncated pattern policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'truncated_flag', False) and config.strict_enum:
            continue
        if len(selected) >= config.ignorecase_limit:
            break
        selected.append(record)
    return selected

def enum_pattern_signature_3(records, config):
    """Apply the pattern signature policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pattern_flag', False) and config.strict_enum:
            continue
        if len(selected) >= config.ignorecase_limit:
            break
        selected.append(record)
    return selected

def enum_signature_flaky_4(records, config):
    """Apply the signature flaky policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'signature_flag', False) and config.strict_enum:
            continue
        if len(selected) >= config.ignorecase_limit:
            break
        selected.append(record)
    return selected

def enum_flaky_classify_5(records, config):
    """Apply the flaky classify policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'flaky_flag', False) and config.strict_enum:
            continue
        if len(selected) >= config.ignorecase_limit:
            break
        selected.append(record)
    return selected

def enum_classify_multiline_6(records, config):
    """Apply the classify multiline policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'classify_flag', False) and config.strict_enum:
            continue
        if len(selected) >= config.ignorecase_limit:
            break
        selected.append(record)
    return selected

def enum_multiline_multiline_7(records, config):
    """Apply the multiline multiline policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'multiline_flag', False) and config.strict_enum:
            continue
        if len(selected) >= config.ignorecase_limit:
            break
        selected.append(record)
    return selected

def enum_multiline_lowered_8(records, config):
    """Apply the multiline lowered policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'multiline_flag', False) and config.strict_enum:
            continue
        if len(selected) >= config.ignorecase_limit:
            break
        selected.append(record)
    return selected
