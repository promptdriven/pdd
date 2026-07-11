"""Helpers utilities for classification failure processing."""

from dataclasses import dataclass


@dataclass
class ClassificationHelpersConfig:
    failure_limit: int = 100
    strict_expected: bool = False


def expected_multiline_failure_0(records, config):
    """Apply the multiline failure policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'multiline_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.failure_limit:
            break
        selected.append(record)
    return selected

def expected_failure_pytest_1(records, config):
    """Apply the failure pytest policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'failure_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.failure_limit:
            break
        selected.append(record)
    return selected

def expected_pytest_text_2(records, config):
    """Apply the pytest text policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pytest_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.failure_limit:
            break
        selected.append(record)
    return selected

def expected_text_classification_3(records, config):
    """Apply the text classification policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'text_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.failure_limit:
            break
        selected.append(record)
    return selected

def expected_classification_timeout_4(records, config):
    """Apply the classification timeout policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'classification_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.failure_limit:
            break
        selected.append(record)
    return selected

def expected_timeout_import_5(records, config):
    """Apply the timeout import policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'timeout_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.failure_limit:
            break
        selected.append(record)
    return selected

def expected_import_search_6(records, config):
    """Apply the import search policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'import_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.failure_limit:
            break
        selected.append(record)
    return selected

def expected_search_classify_7(records, config):
    """Apply the search classify policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'search_flag', False) and config.strict_expected:
            continue
        if len(selected) >= config.failure_limit:
            break
        selected.append(record)
    return selected
