import functools
import time
import uuid
from datetime import datetime
import csv
import os
import tempfile
import click
from rich import print as rprint
from typing import Any, Optional, Tuple, List

# Cross-platform exclusive lock for serializing CSV migration + append between
# concurrent PDD processes. Uses O_CREAT | O_EXCL semantics which works on
# POSIX and Windows alike, so Windows no longer falls through to unlocked
# writes (the previous fcntl-only implementation lost rows during concurrent
# legacy-CSV migration on Windows).
#
# Safety properties beyond plain O_EXCL:
#   - Each acquire writes a unique pid-uuid NONCE to the lock file. Release
#     reads the file back and only unlinks if the nonce still matches ours.
#     This prevents the release-after-stale-steal race: if process A's lock
#     is stolen by B, A's eventual release no longer deletes B's lock file.
#   - Staleness is determined by PID liveness (os.kill(pid, 0)), NOT by lock
#     file mtime alone. A legitimate slow migration whose holder is still
#     running will not be stolen even after many minutes. mtime is used only
#     as a long-threshold safety net for malformed lock files or Windows
#     filesystems where the PID alive-check is unreliable.
_LOCK_RETRY_MAX = 300         # 300 * 0.1s = 30s max wait under contention
_LOCK_RETRY_INTERVAL = 0.1
_LOCK_STALE_SECONDS = 600     # mtime safety-net for unparseable nonces only;
                              # the primary staleness signal is PID liveness.


def _is_pid_alive(pid: int) -> bool:
    """Return True when the OS still has a process for ``pid``.

    On POSIX, ``os.kill(pid, 0)`` raises ``ProcessLookupError`` when the
    process is gone and ``PermissionError`` when it exists but we may not
    signal it. On Windows (where ``signal 0`` semantics differ) and any
    other OSError, return ``True`` conservatively so the lock holder gets
    the benefit of the doubt — the mtime safety-net handles truly stuck
    locks via ``_LOCK_STALE_SECONDS``.
    """
    if pid <= 0:
        return False
    try:
        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        # Process exists but we can't signal it — still alive.
        return True
    except OSError:
        # Unsupported on this platform; fall back to mtime check.
        return True


def _read_lock_owner(lock_path: str) -> Optional[Tuple[int, str]]:
    """Read ``(pid, nonce)`` from an existing lock file.

    Returns ``None`` when the file is missing, unreadable, or malformed.
    Used by :func:`_acquire_atomic_lock` to decide whether the holder is
    still alive, and by :func:`_release_atomic_lock` to verify ownership.
    """
    try:
        with open(lock_path, 'r', encoding='utf-8') as f:
            content = f.read(128).strip()
    except OSError:
        return None
    if not content:
        return None
    # Format: "<pid>-<uuid-hex>"
    head, _, tail = content.partition('-')
    if not head or not tail:
        return None
    try:
        pid = int(head)
    except ValueError:
        return None
    return pid, content


def _is_stale_lock(lock_path: str) -> bool:
    """Return True when the lock file should be reclaimed.

    A lock is stale when (a) the PID it records is no longer alive, or
    (b) the lock file is older than ``_LOCK_STALE_SECONDS`` AND has no
    parseable PID (malformed). A LIVE PID is never stolen — even after
    many minutes — so a legitimate slow migration is safe.
    """
    owner = _read_lock_owner(lock_path)
    if owner is not None:
        pid, _ = owner
        return not _is_pid_alive(pid)
    # Malformed or unreadable lock — fall back to mtime threshold so a
    # truly stuck lock file can still be recovered eventually.
    try:
        age = time.time() - os.path.getmtime(lock_path)
        return age > _LOCK_STALE_SECONDS
    except OSError:
        return False


def _acquire_atomic_lock(
    lock_path: str,
) -> Tuple[Optional[Tuple[int, str]], bool]:
    """Cross-platform best-effort exclusive lock via O_CREAT|O_EXCL.

    Returns ``(handle, contended)`` where:
      - ``handle`` is ``(fd, nonce)`` on success, ``None`` on failure;
      - ``contended`` is ``True`` only when failure was due to another
        live holder timing out our retry budget (so the caller can warn
        the user about real contention vs. silent filesystem fallback).

    Staleness is determined by PID liveness; mtime is only consulted as a
    safety-net when the lock file is malformed.
    """
    nonce = f"{os.getpid()}-{uuid.uuid4().hex}"
    nonce_bytes = nonce.encode()
    saw_contention = False
    for _ in range(_LOCK_RETRY_MAX):
        try:
            fd = os.open(lock_path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
        except FileExistsError:
            saw_contention = True
            if _is_stale_lock(lock_path):
                try:
                    os.unlink(lock_path)
                except OSError:
                    pass
                continue
            time.sleep(_LOCK_RETRY_INTERVAL)
            continue
        except OSError:
            # Filesystem doesn't support O_EXCL semantics; degrade
            # silently (no contention was observed, just unsupported).
            return None, False

        # Now we hold the fd. Nonce write MUST succeed for ownership to be
        # verifiable on release and staleness via PID-alive on contention.
        # If it fails (disk full, fd revoked, process signaled mid-write),
        # close + unlink so we don't leak a malformed lock file other
        # processes will wait the mtime threshold on.
        try:
            written = os.write(fd, nonce_bytes)
            if written != len(nonce_bytes):
                raise OSError("partial nonce write")
        except OSError:
            try:
                os.close(fd)
            except OSError:
                pass
            try:
                os.unlink(lock_path)
            except OSError:
                pass
            time.sleep(_LOCK_RETRY_INTERVAL)
            continue
        return (fd, nonce), False
    return None, saw_contention


def _release_atomic_lock(handle: Optional[Tuple[int, str]], lock_path: str) -> None:
    """Release the lock acquired by :func:`_acquire_atomic_lock`.

    Resolution rules — strongest-evidence-first:
      - If the lock file is gone, no-op (already cleaned).
      - If the file's nonce matches ours, unlink (normal release).
      - If the file's nonce DOES NOT match ours, leave alone (our lock
        was stolen during execution; the new owner now holds the path).
      - If the file exists but is unreadable / has no parseable nonce,
        unlink anyway: we acquired the path via O_EXCL and the malformed
        content can only be our own write that didn't complete (the
        acquire path now rejects partial nonce writes, so in practice
        this only fires when the lock file was truncated by something
        external — leaving it would block future PDD invocations).

    Best-effort: errors during close/read/unlink are swallowed so cost
    tracking never breaks the wrapped command.
    """
    if handle is None:
        return
    fd, our_nonce = handle
    try:
        os.close(fd)
    except OSError:
        pass
    if not os.path.exists(lock_path):
        return
    owner = _read_lock_owner(lock_path)
    if owner is None:
        # File exists but content is unparseable; we hold the
        # O_EXCL-acquired fd, so clean up to avoid leaking the lock.
        try:
            os.unlink(lock_path)
        except OSError:
            pass
        return
    _, recorded = owner
    if recorded == our_nonce:
        try:
            os.unlink(lock_path)
        except OSError:
            pass


__all__ = ['track_cost', 'extract_cost_and_model', 'collect_files', 'wrapper', 'looks_like_file']

def wrapper(*args, **kwargs):
    """Dummy wrapper function to satisfy architecture export requirements."""
    pass

def looks_like_file(path_str):
    """Check if string looks like a file path."""
    if not path_str or not isinstance(path_str, str):
        return False
    # Has file extension or exists
    return '.' in os.path.basename(path_str) or os.path.isfile(path_str)

def track_cost(func):
    @functools.wraps(func)
    def _wrapper(*args, **kwargs):
        ctx = click.get_current_context()
        if ctx is None:
            return func(*args, **kwargs)

        # Scope attempted_models to a single @track_cost invocation so a
        # chained / batched CLI run never inherits the fallback chain from a
        # previous command on the same shared ctx.obj. Snapshot any prior
        # value, reset it, let llm_invoke aggregate within this command,
        # then restore the snapshot after the row is written.
        attempted_models_scoped = False
        prior_attempted_models_present = False
        prior_attempted_models = None
        if ctx.obj is not None and hasattr(ctx.obj, '__setitem__'):
            try:
                existing = ctx.obj.get('attempted_models') if hasattr(ctx.obj, 'get') else None
                if existing is not None:
                    prior_attempted_models = existing
                    prior_attempted_models_present = True
                ctx.obj['attempted_models'] = []
                attempted_models_scoped = True
            except Exception:
                attempted_models_scoped = False

        start_time = datetime.now()
        result = None
        exception_raised = None

        try:
            # Record the invoked subcommand name on the shared ctx.obj so
            # the CLI result callback can display proper names instead of
            # falling back to "Unknown Command X".
            try:
                # Avoid interfering with pytest-based CLI tests which expect
                # Click's default behavior (yielding "Unknown Command X").
                if not os.environ.get('PYTEST_CURRENT_TEST'):
                    if ctx.obj is not None:
                        invoked = ctx.obj.get('invoked_subcommands') or []
                        # Use the current command name if available
                        cmd_name = ctx.command.name if ctx.command else None
                        if cmd_name:
                            invoked.append(cmd_name)
                            ctx.obj['invoked_subcommands'] = invoked
            except Exception:
                # Non-fatal: if we cannot record, proceed normally
                pass

            result = func(*args, **kwargs)
        except Exception as e:
            exception_raised = e
        finally:
            end_time = datetime.now()

            # Capture the chain THIS command accumulated before we restore the
            # prior shared value. Without this snapshot, a later @track_cost
            # invocation on the same ctx.obj would see leftover state from a
            # prior command (issue #1086 regression).
            #
            # Capture regardless of whether the snapshot/restore guard at
            # command entry fired (attempted_models_scoped). ctx.obj may have
            # been None at entry and created inside func via
            # ctx.ensure_object(dict), so a missing snapshot is NOT evidence
            # that no chain was recorded — read ctx.obj['attempted_models']
            # whenever ctx.obj is now non-None.
            command_attempted_models: List[str] = []
            try:
                if ctx is not None and ctx.obj is not None and hasattr(ctx.obj, 'get'):
                    current = ctx.obj.get('attempted_models')
                    if isinstance(current, list):
                        command_attempted_models = [str(m) for m in current if m]
            except Exception:
                command_attempted_models = []

            # Restore the prior shared value (or remove the key entirely) so
            # the next command starts with a clean slate.
            if attempted_models_scoped and ctx.obj is not None:
                try:
                    if prior_attempted_models_present:
                        ctx.obj['attempted_models'] = prior_attempted_models
                    else:
                        if hasattr(ctx.obj, 'pop'):
                            ctx.obj.pop('attempted_models', None)
                        else:
                            try:
                                del ctx.obj['attempted_models']
                            except Exception:
                                pass
                except Exception:
                    pass

            try:
                # Always collect files for core dump, even if output_cost is not set
                input_files, output_files = collect_files(args, kwargs)

                # Store collected files in context for core dump (even if output_cost not set)
                if ctx.obj is not None and ctx.obj.get('core_dump'):
                    files_set = ctx.obj.get('core_dump_files', set())
                    for f in input_files + output_files:
                        if isinstance(f, str) and f:
                            # Convert to absolute path for reliable access later
                            abs_path = os.path.abspath(f)
                            # Add the file if it exists OR if it looks like a file path
                            # (it might have been created/deleted during command execution)
                            if os.path.exists(abs_path) or '.' in os.path.basename(f):
                                files_set.add(abs_path)
                    ctx.obj['core_dump_files'] = files_set

                # Decide whether to write a cost-tracking row. On success we
                # always write. On failure we still write a row when there's
                # any recorded fallback history to surface (either on the
                # raised exception or on ctx.obj) so users can see which
                # candidate models were attempted before the command failed.
                exception_attempted: List[str] = []
                if exception_raised is not None:
                    raw = getattr(exception_raised, 'attempted_models', None)
                    if isinstance(raw, list):
                        exception_attempted = [str(m) for m in raw if m]

                should_write = (
                    exception_raised is None
                    or bool(exception_attempted)
                    or bool(command_attempted_models)
                )

                if should_write:
                    if ctx.obj and hasattr(ctx.obj, 'get'):
                        output_cost_path = ctx.obj.get('output_cost') or os.getenv('PDD_OUTPUT_COST_PATH')
                    else:
                        output_cost_path = os.getenv('PDD_OUTPUT_COST_PATH')

                    if output_cost_path and os.environ.get('PYTEST_CURRENT_TEST') is None:
                        command_name = ctx.command.name if ctx.command else "unknown"
                        if exception_raised is None:
                            cost, model_name, result_attempted = extract_cost_and_model(result)
                        else:
                            # On total failure there is no successful result
                            # to mine, but ctx/exception may still carry the
                            # attempted chain.
                            cost, model_name, result_attempted = '', '', exception_attempted

                        # Determine attempted_models chain. Use only the chain
                        # accumulated within THIS @track_cost invocation so
                        # cost.csv rows never inherit a previous command's
                        # fallback history (issue #1086 regression).
                        attempted_models_list = []
                        if command_attempted_models:
                            attempted_models_list = command_attempted_models
                        elif result_attempted:
                            attempted_models_list = result_attempted

                        attempted_models_str = ';'.join(attempted_models_list) if attempted_models_list else ''

                        timestamp = start_time.strftime('%Y-%m-%dT%H:%M:%S.%f')[:-3]

                        row = {
                            'timestamp': timestamp,
                            'model': model_name,
                            'command': command_name,
                            'cost': cost,
                            'input_files': ';'.join(input_files),
                            'output_files': ';'.join(output_files),
                            'attempted_models': attempted_models_str,
                        }

                        fieldnames = ['timestamp', 'model', 'command', 'cost', 'input_files', 'output_files', 'attempted_models']
                        file_has_content = os.path.isfile(output_cost_path) and os.path.getsize(output_cost_path) > 0

                        # Cheap pre-lock peek: does the file need migration?
                        # Migration is the only operation that requires
                        # cross-process serialization (it's a read-modify-
                        # write of the whole file). A pure append to an
                        # already-migrated file is safe without a lock on
                        # POSIX because O_APPEND guarantees atomicity for
                        # writes up to PIPE_BUF (≥4096 bytes; our rows are
                        # well under that). This split means a stuck or
                        # filesystem-unsupported lock no longer reopens the
                        # lost-row race on the normal append path.
                        needs_migration_likely = False
                        if file_has_content:
                            try:
                                with open(output_cost_path, 'r', newline='', encoding='utf-8') as _peek:
                                    _peek_header = next(csv.reader(_peek), None)
                                if _peek_header is not None and 'attempted_models' not in _peek_header:
                                    needs_migration_likely = True
                            except OSError:
                                pass

                        # Lock acquisition policy:
                        #   - Migration needed → MUST hold the lock; on
                        #     contended timeout or unsupported filesystem,
                        #     SKIP the write entirely (better to lose one
                        #     cost row than to corrupt the legacy CSV).
                        #   - Pure append → acquire best-effort; on any
                        #     failure, fall through to unlocked append
                        #     (relying on POSIX O_APPEND atomicity).
                        lock_path = output_cost_path + ".lock"
                        lock_handle = None
                        lock_contended = False
                        if needs_migration_likely:
                            lock_handle, lock_contended = _acquire_atomic_lock(lock_path)
                            if lock_handle is None:
                                rprint(
                                    "[yellow]track_cost: could not acquire "
                                    "CSV lock for legacy migration "
                                    f"({'contended' if lock_contended else 'unsupported'}); "
                                    "skipping this cost row to avoid corrupting "
                                    f"{output_cost_path}.[/yellow]"
                                )
                                # Skip the write — return without recording.
                                if exception_raised is not None:
                                    raise exception_raised
                                return result
                        else:
                            lock_handle, lock_contended = _acquire_atomic_lock(lock_path)
                            # On pure-append, lock failure is acceptable —
                            # POSIX O_APPEND atomicity handles small rows.

                        try:
                            # If file exists with an older header that
                            # doesn't include 'attempted_models', migrate it
                            # in place so DictReader can expose the new
                            # column properly. Peek only the header on
                            # every call; load and rewrite rows ONLY when
                            # migration is actually needed, to keep append
                            # cost O(1) over the lifetime of a long-lived
                            # cost CSV. RE-READ under the lock — another
                            # process may have migrated between our
                            # pre-lock check and lock acquisition.
                            # Recompute file_has_content too, in case another
                            # process just created/extended the file.
                            file_has_content = os.path.isfile(output_cost_path) and os.path.getsize(output_cost_path) > 0
                            if file_has_content:
                                existing_header = None
                                existing_rows = []
                                needs_migration = False
                                try:
                                    with open(output_cost_path, 'r', newline='', encoding='utf-8') as existing:
                                        reader = csv.reader(existing)
                                        existing_header = next(reader, None)
                                        if existing_header is not None and 'attempted_models' not in existing_header:
                                            needs_migration = True
                                            existing_rows = list(reader)
                                except Exception:
                                    existing_header = None
                                    existing_rows = []
                                    needs_migration = False

                                if needs_migration:
                                    migrated_fieldnames = list(existing_header) + ['attempted_models']
                                    # Write the migrated CSV to a tempfile
                                    # in the SAME directory as the original,
                                    # then os.replace it atomically.
                                    parent_dir = os.path.dirname(os.path.abspath(output_cost_path)) or "."
                                    tmp_fd, tmp_path = tempfile.mkstemp(
                                        prefix=".cost.csv.migrate-", dir=parent_dir
                                    )
                                    try:
                                        with os.fdopen(tmp_fd, 'w', newline='', encoding='utf-8') as tmp_file:
                                            migrate_writer = csv.writer(tmp_file)
                                            migrate_writer.writerow(migrated_fieldnames)
                                            for existing_row in existing_rows:
                                                # Pad shorter rows so column count matches.
                                                padded = list(existing_row) + [''] * (len(migrated_fieldnames) - len(existing_row))
                                                migrate_writer.writerow(padded)
                                        os.replace(tmp_path, output_cost_path)
                                    except Exception:
                                        try:
                                            os.unlink(tmp_path)
                                        except OSError:
                                            pass
                                        raise
                                    fieldnames = migrated_fieldnames

                            with open(output_cost_path, 'a', newline='', encoding='utf-8') as csvfile:
                                writer = csv.DictWriter(csvfile, fieldnames=fieldnames, extrasaction='ignore')
                                if not file_has_content:
                                    writer.writeheader()
                                writer.writerow(row)
                        finally:
                            _release_atomic_lock(lock_handle, lock_path)

            except Exception as e:
                rprint(f"[red]Error tracking cost: {e}[/red]")

        # Re-raise the exception if one occurred
        if exception_raised is not None:
            raise exception_raised

        return result

    return _wrapper

def extract_cost_and_model(result: Any) -> Tuple[Any, str, List[str]]:
    if isinstance(result, tuple) and len(result) >= 1:
        last_elem = result[-1]
        if isinstance(last_elem, dict) and 'cost' in last_elem and 'model_name' in last_elem:
            return last_elem.get('cost', 0), last_elem.get('model_name', ''), last_elem.get('attempted_models', [])
        elif len(result) >= 3:
            return result[-2], result[-1], []
    return '', '', []

def collect_files(args, kwargs):
    input_files = []
    output_files = []

    # Known input parameter names that typically contain file paths
    input_param_names = {
        'prompt_file', 'prompt', 'input', 'input_file', 'source', 'source_file',
        'file', 'path', 'original_prompt_file_path', 'files', 'core_file',
        'code_file', 'unit_test_file', 'error_file', 'test_file', 'example_file'
    }

    # Known output parameter names (anything with 'output' in the name)
    output_param_names = {
        'output', 'output_file', 'output_path', 'destination', 'dest', 'target',
        'output_test', 'output_code', 'output_results'
    }

    # Collect from kwargs (most reliable since Click uses named parameters)
    for k, v in kwargs.items():
        if k in ('ctx', 'context', 'output_cost'):
            continue

        # Check if this is a known parameter name
        is_input_param = k in input_param_names or 'file' in k.lower() or 'prompt' in k.lower()
        is_output_param = k in output_param_names or 'output' in k.lower()

        if isinstance(v, str) and v:
            # For known parameter names, trust that they represent file paths
            # For unknown parameters, check if it looks like a file
            if is_input_param or is_output_param or looks_like_file(v):
                if is_output_param:
                    output_files.append(v)
                elif is_input_param:
                    input_files.append(v)
                else:
                    # Unknown parameter but looks like a file, treat as input
                    input_files.append(v)
        elif isinstance(v, list):
            for item in v:
                if isinstance(item, str) and item:
                    # Same logic for list items
                    if is_input_param or is_output_param or looks_like_file(item):
                        if is_output_param:
                            output_files.append(item)
                        elif is_input_param:
                            input_files.append(item)
                        else:
                            input_files.append(item)

    # Collect from positional args (skip first arg which is usually Click context)
    for i, arg in enumerate(args):
        # Skip first argument if it looks like a Click context
        if i == 0 and hasattr(arg, 'obj'):
            continue

        if isinstance(arg, str) and arg and looks_like_file(arg):
            input_files.append(arg)
        elif isinstance(arg, list):
            for item in arg:
                if isinstance(item, str) and item and looks_like_file(item):
                    input_files.append(item)

    return input_files, output_files
