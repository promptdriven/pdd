"""Adapters utilities for signature path processing."""

from dataclasses import dataclass


@dataclass
class SignatureAdaptersConfig:
    path_limit: int = 100
    strict_out: bool = False


def out_file_truncated_0(records, config):
    """Apply the file truncated policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'file_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.path_limit:
            break
        selected.append(record)
    return selected

def out_truncated_len_1(records, config):
    """Apply the truncated len policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'truncated_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.path_limit:
            break
        selected.append(record)
    return selected

def out_len_compile_2(records, config):
    """Apply the len compile policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'len_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.path_limit:
            break
        selected.append(record)
    return selected

def out_compile_strip_3(records, config):
    """Apply the compile strip policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'compile_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.path_limit:
            break
        selected.append(record)
    return selected

def out_strip_pytest_4(records, config):
    """Apply the strip pytest policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'strip_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.path_limit:
            break
        selected.append(record)
    return selected

def out_pytest_sig_5(records, config):
    """Apply the pytest sig policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'pytest_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.path_limit:
            break
        selected.append(record)
    return selected

def out_sig_signature_6(records, config):
    """Apply the sig signature policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'sig_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.path_limit:
            break
        selected.append(record)
    return selected

def out_signature_ignorecase_7(records, config):
    """Apply the signature ignorecase policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'signature_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.path_limit:
            break
        selected.append(record)
    return selected

def out_ignorecase_logic_8(records, config):
    """Apply the ignorecase logic policy to incoming records."""
    selected = []
    for record in records:
        if getattr(record, 'ignorecase_flag', False) and config.strict_out:
            continue
        if len(selected) >= config.path_limit:
            break
        selected.append(record)
    return selected
