"""
edit_file_tool: A library for programmatic, LLM-driven file editing.

This package provides a clean, stable public API for performing asynchronous
file edits and integrating with tool-calling frameworks.

Primary API:
- edit_file: The core async function for applying edits to files.
- EditTool20250124: The tool definition class for LLM integration.

For CLI usage, refer to the `edit-file-tool` entry point.
"""

import importlib.metadata as importlib_metadata

# 1. Package Metadata
__title__ = "edit-file-tool"
try:
    __version__ = importlib_metadata.version("edit-file-tool")
except importlib_metadata.PackageNotFoundError:
    __version__ = "0.0.0"

# 2. Public API Re-exports
# We attempt to import from .core (src/edit_file_tool/core.py)
# Robustness: Failures occur at call-time/usage-time rather than import-time.

try:
    from .core import edit_file
except ImportError:
    def edit_file(*args, **kwargs):
        """
        Fallback function if the core module cannot be imported.
        Raises RuntimeError as per package contract.
        """
        raise RuntimeError("edit_file_tool.core could not be imported")

try:
    from .core import EditTool20250124
except ImportError:
    # Set to None to allow hasattr() checks and graceful degradation
    EditTool20250124 = None

# 3. Export Control
# __all__ is static to aid IDEs and static analysis tools.
__all__ = [
    "edit_file",
    "EditTool20250124",
    "__version__",
    "__title__",
]

# Note for Tests:
# 1. Verify 'from edit_file_tool import edit_file, EditTool20250124' works in a clean env.
# 2. Verify 'edit_file_tool.__version__' returns a string (e.g., "0.0.0" if not installed).
# 3. Verify calling edit_file raises RuntimeError if core.py is missing/broken.