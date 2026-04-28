"""Bounded wrappers for keyring operations.

Python's keyring library has no timeout. On a locked macOS keychain in
headless CI/SSH, the underlying operation can block waiting for GUI input
that will never arrive. Running keyring operations in daemon threads lets the
caller degrade gracefully while still allowing the process to exit.
"""
from __future__ import annotations

import sys
import threading
from typing import Any, Callable, Dict, Optional, Tuple


_KEYRING_TIMEOUT_DARWIN = 5.0
_KEYRING_TIMEOUT_OTHER = 10.0


def _keyring_op_with_timeout(
    op: Callable[..., Any],
    *args: Any,
    timeout: Optional[float] = None,
) -> Tuple[bool, Any, Optional[BaseException]]:
    """Run a keyring operation in a daemon thread, bounded by timeout seconds.

    Returns ``(timed_out, value, exception)``. The thread is a daemon so a
    still-blocking keyring call cannot prevent process exit.
    """
    if timeout is None:
        timeout = (
            _KEYRING_TIMEOUT_DARWIN if sys.platform == "darwin" else _KEYRING_TIMEOUT_OTHER
        )

    state: Dict[str, Any] = {"value": None, "exception": None, "completed": False}

    def _runner() -> None:
        try:
            state["value"] = op(*args)
        except Exception as exc:  # pylint: disable=broad-exception-caught
            state["exception"] = exc
        except BaseException as exc:  # pylint: disable=broad-exception-caught
            state["exception"] = exc
        finally:
            state["completed"] = True

    thread = threading.Thread(target=_runner, daemon=True, name="keyring-timeout-op")
    thread.start()
    thread.join(timeout=timeout)

    if not state["completed"]:
        return True, None, None
    exception = state["exception"]
    if exception is not None and not isinstance(exception, Exception):
        assert isinstance(exception, BaseException)
        raise exception  # pylint: disable=raising-bad-type
    return False, state["value"], exception
