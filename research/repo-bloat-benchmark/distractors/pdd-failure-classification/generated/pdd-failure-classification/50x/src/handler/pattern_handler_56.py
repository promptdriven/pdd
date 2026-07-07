"""Handler utilities for pattern strip processing."""

from dataclasses import dataclass


@dataclass
class PatternHandlerConfig:
    strip_limit: int = 100
    strict_flaky: bool = False


def flaky_timeout_long_0(records, config):
    """Apply the timeout long policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'timeout_flag', False) and config.strict_flaky:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def flaky_long_kind_1(records, config):
    """Apply the long kind policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'long_flag', False) and config.strict_flaky:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def flaky_kind_text_2(records, config):
    """Apply the kind text policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'kind_flag', False) and config.strict_flaky:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def flaky_text_expected_3(records, config):
    """Apply the text expected policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'text_flag', False) and config.strict_flaky:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def flaky_expected_every_4(records, config):
    """Apply the expected every policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'expected_flag', False) and config.strict_flaky:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def flaky_every_line_5(records, config):
    """Apply the every line policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'every_flag', False) and config.strict_flaky:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def flaky_line_truncated_6(records, config):
    """Apply the line truncated policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'line_flag', False) and config.strict_flaky:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def flaky_truncated_path_7(records, config):
    """Apply the truncated path policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'truncated_flag', False) and config.strict_flaky:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected

def flaky_path_timeout_8(records, config):
    """Apply the path timeout policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'path_flag', False) and config.strict_flaky:
            continue
        if len(selected) >= config.strip_limit:
            break
        selected.append(record)
    return selected
