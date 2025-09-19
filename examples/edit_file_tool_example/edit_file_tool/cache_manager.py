# edit_file_tool/cache_manager.py

"""
Manages smart caching decisions for the Edit File Tool.

This module provides the CacheManager class, which encapsulates the logic for
determining whether to use Anthropic's prompt caching for a given file edit.
It supports user-defined overrides ('always', 'never') and an 'auto' mode
that analyzes file characteristics to make an intelligent decision, optimizing
for cost and performance.

The auto-detection logic is based on file size and content complexity,
following best practices for prompt caching where larger, more complex
contexts benefit the most.

Reference:
- Anthropic Prompt Caching: https://docs.anthropic.com/en/docs/build-with-claude/prompt-caching
"""

from typing import Union

# --- Constants for Auto-Detection Logic ---

# Files smaller than this are unlikely to benefit from caching, as the overhead
# of a cache write might not be offset by savings on subsequent reads.
# The minimum cacheable prompt for many Claude models is 1024 or 2048 tokens,
# so 1KB is a safe and simple lower bound.
SMALL_FILE_THRESHOLD_BYTES: int = 1 * 1024  # 1 KB

# Files larger than this are almost always good candidates for caching, as they
# represent a significant portion of the prompt's token count. Caching them
# provides substantial cost and latency savings on subsequent edits.
LARGE_FILE_THRESHOLD_BYTES: int = 4 * 1024  # 4 KB

# --- Constants for Complexity Heuristic (for medium-sized files) ---

# A file with many lines is more likely to be a structured document (like code
# or configuration) where caching the structure is beneficial.
COMPLEXITY_LINE_COUNT_THRESHOLD: int = 50

# This filters out files that have many lines but are mostly empty, focusing on
# lines with actual content.
COMPLEXITY_NON_EMPTY_LINE_COUNT_THRESHOLD: int = 30

# Content density measures the ratio of meaningful characters to total characters.
# A high density suggests less sparse, more information-rich content (e.g., prose,
# dense code) which is a good candidate for caching. A low density might indicate
# heavily indented, sparse code or formatted text where caching is less critical.
COMPLEXITY_DENSITY_THRESHOLD: float = 0.5


class CacheManager:
    """
    Manages the logic for deciding when to use Anthropic's native prompt caching.

    This class provides a centralized place to manage caching rules, making it
    easy to adjust the strategy without changing the core application logic.
    It operates solely on file content, ensuring it has no side effects like
    file I/O.
    """

    def __init__(self) -> None:
        """Initializes the CacheManager."""
        pass

    def should_use_cache(
        self, file_content: str, use_cache_flag: Union[str, bool]
    ) -> bool:
        """
        Determines if caching should be used based on file characteristics and user preference.

        This is the primary interface for the cache management logic. It handles
        explicit user settings first, then falls back to an automatic detection
        algorithm for the 'auto' mode.

        Args:
            file_content: The content of the file to be analyzed.
            use_cache_flag: The user-specified caching preference.
                Accepts:
                - 'always' or True: Always enable caching.
                - 'never' or False: Always disable caching.
                - 'auto': Use smart auto-detection logic.

        Returns:
            True if caching should be enabled, False otherwise.
        """
        if use_cache_flag in (True, "always"):
            return True
        if use_cache_flag in (False, "never"):
            return False

        # --- Auto-detection logic ---
        if use_cache_flag == "auto":
            try:
                file_size_bytes = len(file_content.encode("utf-8"))
            except Exception:
                # In case of encoding errors with unusual content, default to no cache.
                return False

            if file_size_bytes < SMALL_FILE_THRESHOLD_BYTES:
                return False  # Small files are not worth caching.

            if file_size_bytes > LARGE_FILE_THRESHOLD_BYTES:
                return True  # Large files are always worth caching.

            # For medium-sized files, perform a complexity analysis.
            return self._is_complex_enough(file_content)

        # Default to False if the flag is an unrecognized value.
        return False

    def _is_complex_enough(self, file_content: str) -> bool:
        """
        Analyzes a medium-sized file's content to determine if it's complex enough for caching.

        The heuristic is designed to identify files that, despite being of medium
        size, contain enough structured or dense content to benefit from caching.
        This helps avoid caching files that are medium-sized but "simple" (e.g.,
        mostly whitespace or empty lines).

        The heuristic combines three metrics, and all must be exceeded:
        1.  **Line Count:** The file must have more lines than the threshold.
        2.  **Non-Empty Line Count:** It must have more lines with content than the threshold.
        3.  **Content Density:** The ratio of non-whitespace to total characters
            must exceed a certain threshold.

        Args:
            file_content: The content of the file.

        Returns:
            True if the file is deemed complex, False otherwise.
        """
        if not file_content:
            return False

        # Calculate metrics for complexity analysis
        lines = file_content.splitlines()
        line_count: int = len(lines)
        non_empty_line_count: int = sum(1 for line in lines if line.strip())

        total_chars: int = len(file_content)
        if total_chars == 0:
            return False

        # Use a more robust method for counting non-whitespace characters that is
        # not dependent on the specific behavior of str.split().
        non_whitespace_chars: int = sum(1 for char in file_content if not char.isspace())
        content_density: float = float(non_whitespace_chars) / total_chars

        # Apply the heuristic
        is_complex = (
            line_count > COMPLEXITY_LINE_COUNT_THRESHOLD
            and non_empty_line_count > COMPLEXITY_NON_EMPTY_LINE_COUNT_THRESHOLD
            and content_density > COMPLEXITY_DENSITY_THRESHOLD
        )

        return is_complex
