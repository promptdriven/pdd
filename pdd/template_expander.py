# pdd/template_expander.py
"""
Template expansion utility for output path configuration.

This module provides a function to expand path templates with placeholders
like {name}, {category}, {ext}, etc. It enables extensible project layouts
for different languages and frameworks (Python, TypeScript, Vue, Go, etc.).

Supported placeholders:
    {name}        - Base name (last segment of input path)
    {category}    - Parent path segments (empty if none)
    {dir_prefix}  - Full input directory prefix with trailing /
    {ext}         - File extension from language (e.g., "py", "tsx")
    {language}    - Full language name (e.g., "python", "typescript")
    {name_snake}  - snake_case version of name
    {name_pascal} - PascalCase version of name
    {name_kebab}  - kebab-case version of name

Example:
    >>> expand_template(
    ...     "frontend/src/components/{category}/{name}/{name}.tsx",
    ...     {"name": "AssetCard", "category": "marketplace"}
    ... )
    'frontend/src/components/marketplace/AssetCard/AssetCard.tsx'
"""

import re
import os
from typing import Dict, Any


def _to_snake_case(s: str) -> str:
    """
    Convert string to snake_case.

    Handles PascalCase, camelCase, and existing snake_case.

    Examples:
        AssetCard -> asset_card
        assetCard -> asset_card
        already_snake -> already_snake
    """
    if not s:
        return s
    # Insert underscore before uppercase letters (except at start)
    result = re.sub(r'(?<!^)(?=[A-Z])', '_', s)
    return result.lower()


def _to_pascal_case(s: str) -> str:
    """
    Convert string to PascalCase.

    Handles snake_case, kebab-case, and existing PascalCase.

    Examples:
        asset_card -> AssetCard
        asset-card -> AssetCard
        AssetCard -> Assetcard (note: re-capitalizes)
    """
    if not s:
        return s
    # Split on underscores, hyphens, or other common delimiters
    parts = re.split(r'[_\-\s]+', s)
    return ''.join(part.title() for part in parts if part)


def _to_kebab_case(s: str) -> str:
    """
    Convert string to kebab-case.

    Handles PascalCase, camelCase, and existing kebab-case.

    Examples:
        AssetCard -> asset-card
        assetCard -> asset-card
        already-kebab -> already-kebab
    """
    if not s:
        return s
    # Insert hyphen before uppercase letters (except at start)
    result = re.sub(r'(?<!^)(?=[A-Z])', '-', s)
    return result.lower()


def _normalize_path(path: str) -> str:
    """
    Normalize a path to remove double slashes and resolve . and ..

    This handles edge cases like empty {category} producing paths like:
    "src/components//Button" -> "src/components/Button"

    Unlike os.path.normpath, this preserves relative paths without
    converting them to absolute paths.
    """
    if not path:
        return path

    # Split path and filter empty segments (which cause double slashes)
    parts = path.split('/')
    normalized_parts = [p for p in parts if p]

    # Rejoin with single slashes
    result = '/'.join(normalized_parts)

    # Use os.path.normpath for additional cleanup (handles . and ..)
    # but it converts to OS-specific separators, so convert back
    result = os.path.normpath(result)

    # On Windows, normpath uses backslashes; convert back to forward slashes
    result = result.replace('\\', '/')

    return result


def expand_template(template: str, context: Dict[str, Any]) -> str:
    """
    Expand a path template with placeholder values.

    Args:
        template: Path template with {placeholder} syntax
        context: Dictionary of values to substitute

    Returns:
        Expanded path with normalized slashes

    Example:
        >>> expand_template(
        ...     "frontend/src/components/{category}/{name}/{name}.tsx",
        ...     {"name": "AssetCard", "category": "marketplace"}
        ... )
        'frontend/src/components/marketplace/AssetCard/AssetCard.tsx'
    """
    # Get base values from context (with empty string defaults)
    name = context.get('name', '')
    category = context.get('category', '')
    dir_prefix = context.get('dir_prefix', '')
    ext = context.get('ext', '')
    language = context.get('language', '')

    # Build the full set of available placeholders
    placeholders = {
        'name': name,
        'category': category,
        'dir_prefix': dir_prefix,
        'ext': ext,
        'language': language,
        'name_snake': _to_snake_case(name),
        'name_pascal': _to_pascal_case(name),
        'name_kebab': _to_kebab_case(name),
    }

    # Perform substitution
    result = template
    for key, value in placeholders.items():
        result = result.replace(f'{{{key}}}', str(value))

    # Normalize the path to handle empty segments (double slashes)
    result = _normalize_path(result)

    return result
