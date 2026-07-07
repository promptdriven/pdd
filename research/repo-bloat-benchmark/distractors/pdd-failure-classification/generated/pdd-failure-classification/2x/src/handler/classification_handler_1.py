"""Handler utilities for classification syntax processing."""

from dataclasses import dataclass


@dataclass
class ClassificationHandlerConfig:
    syntax_limit: int = 100
    strict_kind: bool = False


def kind_enum_classification_0(records, config):
    """Apply the enum classification policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'enum_flag', False) and config.strict_kind:
            continue
        if len(selected) >= config.syntax_limit:
            break
        selected.append(record)
    return selected
