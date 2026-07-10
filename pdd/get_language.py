"""Compatibility language lookup backed by the protected bundled registry."""

from pdd.sync_core import LanguageRegistry, LanguageRegistryError

def get_language(extension: str) -> str:
    """
    Determines the programming language associated with a given file extension.

    Args:
        extension (str): The file extension to look up.

    Returns:
        str: The name of the programming language or an empty string if not found.

    Raises:
        ValueError: If PDD_PATH environment variable is not set.
    """
    if not extension:
        return ""
    try:
        return LanguageRegistry.bundled().resolve_extension(extension).display_name
    except LanguageRegistryError:
        return ""
