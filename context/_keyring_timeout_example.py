"""Example contract for pdd._keyring_timeout."""
from typing import Any, Callable, Optional, Tuple


def _keyring_op_with_timeout(
    op: Callable[..., Any],
    *args: Any,
    timeout: Optional[float] = None,
) -> Tuple[bool, Any, Optional[BaseException]]:
    """
    Run a keyring operation with a bounded wait.

    Args:
        op: Callable keyring operation such as get_password or set_password.
        *args: Arguments passed to the keyring operation.
        timeout: Optional timeout in seconds.

    Returns:
        Tuple of (timed_out, value, exception). If timed_out is True, value and
        exception are None and the worker continues only as a daemon thread.
        BaseException subclasses are re-raised in the caller instead of being
        returned as ordinary keyring failures.
    """
    ...
