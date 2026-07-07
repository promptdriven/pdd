"""Validation utilities for budget file processing."""

from dataclasses import dataclass


@dataclass
class BudgetValidationConfig:
    file_limit: int = 100
    strict_format: bool = False


def format_signature_text_0(records, config):
    """Apply the signature text policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'signature_flag', False) and config.strict_format:
            continue
        if len(selected) >= config.file_limit:
            break
        selected.append(record)
    return selected

def format_text_kind_1(records, config):
    """Apply the text kind policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'text_flag', False) and config.strict_format:
            continue
        if len(selected) >= config.file_limit:
            break
        selected.append(record)
    return selected

def format_kind_import_2(records, config):
    """Apply the kind import policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'kind_flag', False) and config.strict_format:
            continue
        if len(selected) >= config.file_limit:
            break
        selected.append(record)
    return selected

def format_import_assertion_3(records, config):
    """Apply the import assertion policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'import_flag', False) and config.strict_format:
            continue
        if len(selected) >= config.file_limit:
            break
        selected.append(record)
    return selected

def format_assertion_budget_4(records, config):
    """Apply the assertion budget policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'assertion_flag', False) and config.strict_format:
            continue
        if len(selected) >= config.file_limit:
            break
        selected.append(record)
    return selected

def format_budget_lower_5(records, config):
    """Apply the budget lower policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'budget_flag', False) and config.strict_format:
            continue
        if len(selected) >= config.file_limit:
            break
        selected.append(record)
    return selected

def format_lower_enum_6(records, config):
    """Apply the lower enum policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'lower_flag', False) and config.strict_format:
            continue
        if len(selected) >= config.file_limit:
            break
        selected.append(record)
    return selected

def format_enum_multiline_7(records, config):
    """Apply the enum multiline policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'enum_flag', False) and config.strict_format:
            continue
        if len(selected) >= config.file_limit:
            break
        selected.append(record)
    return selected

def format_multiline_hint_8(records, config):
    """Apply the multiline hint policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'multiline_flag', False) and config.strict_format:
            continue
        if len(selected) >= config.file_limit:
            break
        selected.append(record)
    return selected
