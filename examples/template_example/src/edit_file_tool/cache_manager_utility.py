"""Cache manager utility for determining when to use prompt caching.

This module determines whether Anthropic native prompt caching should be enabled
for a given file edit request. It obeys user preference overrides and uses
size and lightweight complexity heuristics for medium-sized files.
"""

import logging
from pathlib import Path
from typing import Dict, Tuple, Union

logger = logging.getLogger(__name__)

__all__ = ["should_use_cache"]

SMALL_FILE_BYTES = 1024
LARGE_FILE_BYTES = 4096
SAMPLE_BYTES = 16384
MEDIUM_FALLBACK_BYTES = 3072

_COMPLEXITY_THRESHOLD_LINE_COUNT = 80
_COMPLEXITY_THRESHOLD_RATIO = 0.6
_COMPLEXITY_THRESHOLD_LINE_LENGTH = 35


def should_use_cache(file_path: str, file_size: int, use_cache: Union[str, bool] = "auto") -> bool:
    """Return whether prompt caching should be enabled for a file edit request.

    Args:
        file_path: The path to the file being edited. Must be a non-empty string.
        file_size: The size of the file in bytes. Must be an int >= 0.
        use_cache: Preference for caching. Accepts True/False or strings
            "auto" (default), "always", "never" (case-insensitive).

    Returns:
        True if prompt caching should be enabled; False otherwise.
    """

    normalized = _normalize_use_cache(use_cache)
    _validate_inputs(file_path, file_size)

    if normalized is True:
        logger.debug("use_cache override: always enable cache (bool True)")
        return True
    if normalized is False:
        logger.debug("use_cache override: explicitly disable cache (bool False)")
        return False

    return _should_cache_auto(file_path, file_size)


def _normalize_use_cache(value: Union[str, bool]) -> Union[str, bool]:
    if isinstance(value, bool):
        return value

    if isinstance(value, str):
        normalized = value.strip().lower()
        if normalized in {"auto", "always", "never"}:
            if normalized == "always":
                return True
            if normalized == "never":
                return False
            return "auto"
        raise ValueError(
            "use_cache must be one of 'auto', 'always', 'never', True, or False"
        )

    raise ValueError("use_cache must be a string mode or boolean value")


def _validate_inputs(file_path: str, file_size: int) -> None:
    if not isinstance(file_path, str) or not file_path.strip():
        raise ValueError("file_path must be a non-empty string")
    if not isinstance(file_size, int) or isinstance(file_size, bool):
        raise ValueError("file_size must be an int >= 0")
    if file_size < 0:
        raise ValueError("file_size must be an int >= 0")


def _should_cache_auto(file_path: str, file_size: int) -> bool:
    logger.debug("auto cache decision: file=%s size=%d", file_path, file_size)

    if file_size < SMALL_FILE_BYTES:
        logger.debug("size below SMALL_FILE_BYTES (%d): disable cache", SMALL_FILE_BYTES)
        return False
    if file_size > LARGE_FILE_BYTES:
        logger.debug("size above LARGE_FILE_BYTES (%d): enable cache", LARGE_FILE_BYTES)
        return True

    sample_text, metrics = _sample_and_compute_metrics(file_path)

    if metrics is None:
        decision = file_size >= MEDIUM_FALLBACK_BYTES
        logger.debug(
            "sample unavailable, fallback decision based on size >= %d: %s",
            MEDIUM_FALLBACK_BYTES,
            decision,
        )
        return decision

    decision = (
        metrics["line_count"] >= _COMPLEXITY_THRESHOLD_LINE_COUNT
        or (
            metrics["non_empty_ratio"] >= _COMPLEXITY_THRESHOLD_RATIO
            and metrics["avg_line_length"] >= _COMPLEXITY_THRESHOLD_LINE_LENGTH
        )
        or file_size >= MEDIUM_FALLBACK_BYTES
    )

    logger.debug(
        "metrics=%s decision=%s", metrics, decision
    )

    return decision


def _sample_and_compute_metrics(file_path: str) -> Tuple[str, Union[Dict[str, float], None]]:
    try:
        path = Path(file_path)
        if not path.exists():
            logger.debug("sample read: file missing (%s)", file_path)
            return "", None

        text = path.read_text(encoding="utf-8", errors="ignore")[:SAMPLE_BYTES]
    except OSError as exc:
        logger.debug("sample read failed for %s: %s", file_path, exc)
        return "", None

    metrics = _compute_complexity_metrics(text)
    return text, metrics


def _compute_complexity_metrics(sample_text: str) -> Dict[str, float]:
    lines = sample_text.splitlines()
    line_count = len(lines)
    non_empty_lines = sum(1 for line in lines if line.strip())

    if line_count == 0:
        non_empty_ratio = 0.0
        avg_line_length = 0.0
        code_density = 0.0
    else:
        non_empty_ratio = non_empty_lines / line_count
        total_chars = sum(len(line) for line in lines)
        avg_line_length = total_chars / line_count
        non_space_chars = sum(len(line.replace(" ", "")) for line in lines)
        code_density = non_space_chars / total_chars if total_chars else 0.0

    return {
        "line_count": float(line_count),
        "non_empty_ratio": non_empty_ratio,
        "avg_line_length": avg_line_length,
        "code_density": code_density,
    }


# Unit-test plan (small focused plan):
# 1. Confirm 'always' string and True override caching regardless of file size.
# 2. Confirm 'never' string and False override disabling regardless of file size.
# 3. Validate threshold edges: size=1023 -> False, size=1024 -> medium heuristics,
#    size=4096 -> medium heuristics, size=4097 -> True.
# 4. Reject invalid use_cache values (e.g., 'invalid') and invalid file_size (negative or non-int).
# 5. Empty or whitespace-only file_path should raise ValueError.
# 6. Medium-size auto mode missing file should fall back to size rule (>=3072 -> True else False) without raising.