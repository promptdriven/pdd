"""
Helper utilities for architecture sync filename normalization.

Provides the ``filepath_to_prompt_filename`` function used by
``architecture_sync.normalize_architecture_filenames`` to derive prompt
filenames that mirror the output filepath directory structure (Issue #617).
"""

import os
import pathlib


def filepath_to_prompt_filename(filepath: str, language: str) -> str:
    """
    Compute the prompt filename from a given output filepath and language.

    The prompt filename mirrors the directory structure of the filepath so
    that prompts are organized the same way as the source tree.

    Args:
        filepath: The target output path (e.g., "app/api/route.ts").
        language: The PascalCase programming language (e.g., "TypeScript").

    Returns:
        A string representing the prompt filename path with forward slashes.
    """
    path = pathlib.Path(filepath)

    directory = path.parent
    filename_stem = path.stem

    new_filename = f"{filename_stem}_{language}.prompt"

    if directory == pathlib.Path('.'):
        result_path = new_filename
    else:
        result_path = directory / new_filename

    return str(result_path).replace(os.sep, '/')
