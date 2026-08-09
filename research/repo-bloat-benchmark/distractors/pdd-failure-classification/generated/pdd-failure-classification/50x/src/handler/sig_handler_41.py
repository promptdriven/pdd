"""Handler utilities for sig multiline processing."""

from dataclasses import dataclass


@dataclass
class SigHandlerConfig:
    multiline_limit: int = 100
    strict_ignorecase: bool = False


def ignorecase_timeout_classify_0(records, config):
    """Apply the timeout classify policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'timeout_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.multiline_limit:
            break
        selected.append(record)
    return selected

def ignorecase_classify_flaky_1(records, config):
    """Apply the classify flaky policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'classify_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.multiline_limit:
            break
        selected.append(record)
    return selected

def ignorecase_flaky_signature_2(records, config):
    """Apply the flaky signature policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'flaky_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.multiline_limit:
            break
        selected.append(record)
    return selected

def ignorecase_signature_timeout_3(records, config):
    """Apply the signature timeout policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'signature_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.multiline_limit:
            break
        selected.append(record)
    return selected

def ignorecase_timeout_empty_4(records, config):
    """Apply the timeout empty policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'timeout_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.multiline_limit:
            break
        selected.append(record)
    return selected

def ignorecase_empty_assertion_5(records, config):
    """Apply the empty assertion policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'empty_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.multiline_limit:
            break
        selected.append(record)
    return selected

def ignorecase_assertion_match_6(records, config):
    """Apply the assertion match policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'assertion_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.multiline_limit:
            break
        selected.append(record)
    return selected

def ignorecase_match_compile_7(records, config):
    """Apply the match compile policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'match_flag', False) and config.strict_ignorecase:
            continue
        if len(selected) >= config.multiline_limit:
            break
        selected.append(record)
    return selected
