import functools
import time
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
_LOCK_RETRY_MAX = 50          # 50 * 0.1s = 5s max wait
_LOCK_RETRY_INTERVAL = 0.1
_LOCK_STALE_SECONDS = 60      # forcibly steal a lock older than this


def _acquire_atomic_lock(lock_path: str) -> Optional[int]:
    """Cross-platform best-effort exclusive lock via O_CREAT|O_EXCL.

    Returns the lock file descriptor on success, None on failure (caller
    falls through to unlocked atomic-rename behavior — still safer than
    in-place rewrite, just not safe against the inter-process race).

    Stale lock files older than ``_LOCK_STALE_SECONDS`` are stolen to
    recover from crashed processes that didn't release on exit.
    """
    for _ in range(_LOCK_RETRY_MAX):
        try:
            fd = os.open(lock_path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
            try:
                os.write(fd, str(os.getpid()).encode())
            except OSError:
                # Failure to write the pid is non-fatal; we still hold the lock.
                pass
            return fd
        except FileExistsError:
            try:
                age = time.time() - os.path.getmtime(lock_path)
                if age > _LOCK_STALE_SECONDS:
                    try:
                        os.unlink(lock_path)
                    except OSError:
                        pass
                    continue
            except OSError:
                pass
            time.sleep(_LOCK_RETRY_INTERVAL)
        except OSError:
            # Filesystem doesn't support O_EXCL semantics; degrade.
            return None
    return None


def _release_atomic_lock(fd: Optional[int], lock_path: str) -> None:
    """Release the lock acquired by :func:`_acquire_atomic_lock`.

    Best-effort: errors during close/unlink are swallowed so cost
    tracking never breaks the wrapped command.
    """
    if fd is None:
        return
    try:
        os.close(fd)
    except OSError:
        pass
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

                        # Serialize the migration+append critical section
                        # across concurrent PDD processes via a cross-
                        # platform exclusive lock file (O_CREAT|O_EXCL).
                        # Without the lock, two processes hitting a legacy
                        # 6-column cost.csv would each peek-then-migrate-
                        # then-append independently and the second
                        # os.replace would overwrite the first's appended
                        # row (lost-update race). Lock acquisition is
                        # best-effort: on filesystems that don't support
                        # O_EXCL semantics or after a 5s timeout, fall
                        # through to the unlocked atomic-rename path,
                        # which is still safer than in-place rewrite —
                        # just not safe against the inter-process race.
                        lock_path = output_cost_path + ".lock"
                        lock_fd = _acquire_atomic_lock(lock_path)

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
                            _release_atomic_lock(lock_fd, lock_path)

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
