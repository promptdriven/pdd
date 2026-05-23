import functools
from datetime import datetime, timezone
import csv
import os
import uuid
import click
from rich import print as rprint
from typing import Any, List, Tuple

try:
    import fcntl  # POSIX-only; absent on Windows
    _HAVE_FCNTL = True
except ImportError:  # pragma: no cover - non-POSIX hosts
    fcntl = None  # type: ignore[assignment]
    _HAVE_FCNTL = False

# Tracks cost-CSV paths we've already warned the user about for the
# "legacy header, attempted_models column will be omitted" case. Keyed on
# absolute path so a long-running session doesn't spam the same notice.
_legacy_csv_warned: set = set()


class _WriteLock:
    """Best-effort POSIX file lock around an ENTIRE cost-CSV write.

    Serialises the read-header → maybe-migrate → append-row block per
    file so concurrent writers cannot lose data via the migration
    race: previously a contending writer would fall back to a legacy
    append while the lock-holder's migration replaced the file with a
    pre-append snapshot, silently deleting the contender's row. The
    lock now spans the full write block, not just the migration —
    contenders block on ``LOCK_EX`` and serialise.

    The sidecar lock file is NEVER unlinked. Unlinking lets a later
    process open a new inode at the same path while the previous
    holder is still closing the OLD inode, so two processes can end
    up holding exclusive locks on different inodes for the "same"
    lock path. The lock file is tiny (effectively empty); leaving it
    in place is the correct trade-off for soundness.

    On non-POSIX hosts (no ``fcntl``), the context manager yields
    ``False`` so callers know the lock is unenforced. Callers MUST
    still proceed with the write — the platform simply does not
    guarantee atomic concurrent appends in that case.
    """

    def __init__(self, csv_path: str) -> None:
        self._csv_path = csv_path
        self._lock_path = csv_path + ".migrate.lock"
        self._fh = None
        self._acquired = False

    def __enter__(self) -> bool:
        if not _HAVE_FCNTL:
            return False
        try:
            # Ensure parent dir exists (the CSV may not be created yet).
            os.makedirs(os.path.dirname(self._lock_path) or ".", exist_ok=True)
            # 'a+b' opens-or-creates without truncating, giving a stable
            # inode for the path across the lifetime of all callers as
            # long as nobody unlinks it. We don't unlink (see class
            # docstring).
            self._fh = open(self._lock_path, "a+b")
            # Blocking LOCK_EX: contenders wait, then proceed serially.
            # Non-blocking (LOCK_NB) is the wrong choice here — it lets
            # contenders skip the lock and race the holder's write,
            # which is exactly the data-loss bug we are fixing.
            fcntl.flock(self._fh.fileno(), fcntl.LOCK_EX)
            self._acquired = True
            return True
        except Exception:  # noqa: BLE001 — broad catch covers OSError,
            # TypeError (mock-open fileno returns non-int in tests), and
            # any other surprise from the fcntl/open layer. In all
            # error cases the right behaviour is to proceed without the
            # lock; track_cost's CSV write is best-effort and should
            # never crash the wrapped command.
            if self._fh is not None:
                try:
                    self._fh.close()
                except Exception:  # noqa: BLE001
                    pass
                self._fh = None
            return False

    def __exit__(self, exc_type, exc_val, exc_tb) -> None:
        if self._fh is not None:
            if self._acquired:
                try:
                    fcntl.flock(self._fh.fileno(), fcntl.LOCK_UN)
                except OSError:
                    pass
            try:
                self._fh.close()
            except OSError:
                pass
            self._fh = None
        # DO NOT unlink the sidecar lock file — see class docstring.


# Backwards-compatible alias for the old name (some tests may still
# reference it). The class no longer skips on contention; it blocks.
_MigrationLock = _WriteLock


def _unique_tmp_path(path: str) -> str:
    """Per-writer tmp filename so two concurrent migrations do not
    clobber a single shared ``*.migrate.tmp``.
    """
    return f"{path}.migrate.tmp.{os.getpid()}.{uuid.uuid4().hex}"


def _migrate_legacy_to_new_header(path: str) -> None:
    """Rewrite an oldest-format cost CSV in place to add both the
    ``attempted_models`` and ``job_id`` columns.

    Same migration story as :func:`_migrate_mid_to_new_header`: triggered
    only when a server-managed run (``PDD_JOB_ID`` non-empty) writes to a
    pre-existing legacy file, so two same-command jobs sharing that file
    can be attributed via the watcher's strict ``job_id`` filter rather
    than collapsing under the command + timestamp fallback (where each
    counts the other's spend).

    Existing rows get empty ``attempted_models`` and ``job_id`` cells;
    the legacy fallback in the watcher then treats them as "untagged"
    rows that do not match any active job's filter, so old rows do not
    contaminate new jobs' spend.
    """
    """Caller MUST hold ``_WriteLock(path)`` while invoking this helper.
    See the helper class docstring for why the lock spans the entire
    write block (not just the migration itself)."""
    legacy_fieldnames = [
        'timestamp', 'model', 'command', 'cost',
        'input_files', 'output_files',
    ]
    new_fieldnames = legacy_fieldnames + ['attempted_models', 'job_id']
    tmp_path = _unique_tmp_path(path)
    try:
        with open(path, 'r', encoding='utf-8', newline='') as src:
            reader = csv.DictReader(src)
            rows = list(reader)
        with open(tmp_path, 'w', encoding='utf-8', newline='') as dst:
            writer = csv.DictWriter(dst, fieldnames=new_fieldnames)
            writer.writeheader()
            for r in rows:
                r.setdefault('attempted_models', '')
                r.setdefault('job_id', '')
                writer.writerow({k: r.get(k, '') for k in new_fieldnames})
        os.replace(tmp_path, path)
    except OSError as exc:
        try:
            os.unlink(tmp_path)
        except OSError:
            pass
        rprint(
            f"[yellow]Could not migrate legacy cost CSV {path} to add "
            f"attempted_models + job_id columns: {exc}. Per-job isolation "
            f"will degrade to command+timestamp filtering for this file."
            f"[/yellow]"
        )


def _migrate_mid_to_new_header(path: str) -> None:
    """Rewrite a mid-format cost CSV in place to add the ``job_id`` column.

    The CSV reader contract permits a one-time legacy-header migration
    when the server needs per-job isolation; without this, two same-
    command jobs sharing a pre-existing mid-format CSV would each
    count the other's spend because the watcher's ``job_id`` filter
    requires the column to be present in the header.

    Atomic via ``os.replace`` of a temp file. Existing rows get an
    empty ``job_id`` value, so they fall under the "untagged" cohort
    that the watcher's legacy fallback handles via command+timestamp.
    Safe under one writer; concurrent writers to the same CSV are a
    misuse case the reader contract already calls out.
    """
    """Caller MUST hold ``_WriteLock(path)`` while invoking this helper.
    See the helper class docstring for why the lock spans the entire
    write block (not just the migration itself)."""
    legacy_fieldnames = [
        'timestamp', 'model', 'command', 'cost',
        'input_files', 'output_files',
    ]
    mid_fieldnames = legacy_fieldnames + ['attempted_models']
    new_fieldnames = mid_fieldnames + ['job_id']
    tmp_path = _unique_tmp_path(path)
    try:
        with open(path, 'r', encoding='utf-8', newline='') as src:
            reader = csv.DictReader(src)
            rows = list(reader)
        with open(tmp_path, 'w', encoding='utf-8', newline='') as dst:
            writer = csv.DictWriter(dst, fieldnames=new_fieldnames)
            writer.writeheader()
            for r in rows:
                r.setdefault('job_id', '')
                # Drop any unknown columns the reader picked up so the
                # writer does not raise on extras.
                writer.writerow({k: r.get(k, '') for k in new_fieldnames})
        os.replace(tmp_path, path)
    except OSError as exc:
        # Best-effort: if migration fails (perms, disk full), fall back
        # to the legacy-fallback path. Clean up the temp file.
        try:
            os.unlink(tmp_path)
        except OSError:
            pass
        rprint(
            f"[yellow]Could not migrate cost CSV {path} to add job_id "
            f"column: {exc}. Per-job isolation will degrade to "
            f"command+timestamp filtering for this file.[/yellow]"
        )


def looks_like_file(path_str) -> bool:
    """Check if string looks like a file path."""
    if not path_str or not isinstance(path_str, str):
        return False
    return '.' in os.path.basename(path_str) or os.path.isfile(path_str)

def track_cost(func):
    @functools.wraps(func)
    def wrapper(*args, **kwargs):
        ctx = click.get_current_context()
        if ctx is None:
            return func(*args, **kwargs)

        # Timestamps written to the cost CSV must be timezone-aware UTC so
        # downstream readers (notably `pdd.cost_budget_watcher`) can compare
        # them against the aware `job.started_at` the server records without
        # raising or — worse — silently misattributing rows after a naive ->
        # UTC reinterpretation. The reader-contract section below documents
        # ISO 8601 UTC; this assignment honors it.
        start_time = datetime.now(timezone.utc)
        result = None
        exception_raised = None

        # Snapshot any prior `attempted_models` so it cannot leak from an
        # earlier tracked command into this one. We clear it before invoking
        # the wrapped command and restore the prior value (or remove the key)
        # after the row is written.
        prior_attempted_models = None
        had_prior_attempted_models = False
        try:
            if ctx.obj is not None and isinstance(ctx.obj, dict) and 'attempted_models' in ctx.obj:
                prior_attempted_models = ctx.obj.pop('attempted_models')
                had_prior_attempted_models = True
        except Exception:
            pass

        try:
            try:
                if not os.environ.get('PYTEST_CURRENT_TEST'):
                    if ctx.obj is not None:
                        invoked = ctx.obj.get('invoked_subcommands') or []
                        cmd_name = ctx.command.name if ctx.command else None
                        if cmd_name:
                            invoked.append(cmd_name)
                            ctx.obj['invoked_subcommands'] = invoked
            except Exception:
                pass

            result = func(*args, **kwargs)
        except Exception as e:
            exception_raised = e
        finally:
            end_time = datetime.now(timezone.utc)

            try:
                input_files, output_files = collect_files(args, kwargs)

                if ctx.obj is not None and ctx.obj.get('core_dump'):
                    files_set = ctx.obj.get('core_dump_files', set())
                    for f in input_files + output_files:
                        if isinstance(f, str) and f:
                            abs_path = os.path.abspath(f)
                            if os.path.exists(abs_path) or '.' in os.path.basename(f):
                                files_set.add(abs_path)
                    ctx.obj['core_dump_files'] = files_set

                # Write a row regardless of whether the wrapped command
                # raised. A subprocess that spent money and then raised
                # used to be invisible to budget enforcement (the old
                # `if exception_raised is None:` gate skipped the write
                # entirely), so a cap on a flaky job could be bypassed
                # by simply crashing after the LLM call. We now always
                # emit a row, sourcing the cost/model from any partial
                # state that llm_invoke may have accumulated on
                # ctx.obj when the wrapped command's return tuple is
                # unavailable.
                if ctx.obj and hasattr(ctx.obj, 'get'):
                    output_cost_path = ctx.obj.get('output_cost') or os.getenv('PDD_OUTPUT_COST_PATH')
                else:
                    output_cost_path = os.getenv('PDD_OUTPUT_COST_PATH')

                if output_cost_path and os.environ.get('PYTEST_CURRENT_TEST') is None:
                    command_name = ctx.command.name
                    if exception_raised is None and result is not None:
                        cost, model_name = extract_cost_and_model(result)
                    else:
                        # Failed command: fall back to whatever partial
                        # cost/model llm_invoke pushed to ctx.obj before
                        # the exception propagated. Both keys are
                        # documented contract surface for cross-module
                        # use; missing keys default to 0/empty.
                        cost = (
                            ctx.obj.get('partial_cost', 0.0)
                            if ctx.obj and isinstance(ctx.obj, dict)
                            else 0.0
                        )
                        model_name = (
                            ctx.obj.get('last_model', '')
                            if ctx.obj and isinstance(ctx.obj, dict)
                            else ''
                        )

                    attempted_models_list = ctx.obj.get('attempted_models') if ctx.obj and isinstance(ctx.obj, dict) else None
                    if not attempted_models_list:
                        attempted_models_list = [model_name]
                    attempted_models = ';'.join(str(m).replace(';', ':') for m in attempted_models_list)

                    # Emit ISO 8601 with the tz offset preserved so
                    # readers do not have to guess the timezone. Trim
                    # microseconds to milliseconds to match the legacy
                    # column width.
                    timestamp = start_time.isoformat(timespec='milliseconds')

                    # Per-job attribution column (PDD_JOB_ID set by the
                    # GitHub App's JobManager around each subprocess).
                    # Empty when running outside the server — older
                    # tooling that does not set the env reads/writes
                    # CSVs unchanged.
                    job_id = os.getenv('PDD_JOB_ID', '') or ''

                    row = {
                        'timestamp': timestamp,
                        'model': model_name,
                        'command': command_name,
                        'cost': cost,
                        'input_files': ';'.join(input_files),
                        'output_files': ';'.join(output_files),
                        'attempted_models': attempted_models,
                        'job_id': job_id,
                    }

                    legacy_fieldnames = ['timestamp', 'model', 'command', 'cost', 'input_files', 'output_files']
                    mid_fieldnames = legacy_fieldnames + ['attempted_models']
                    new_fieldnames = mid_fieldnames + ['job_id']

                    # Serialize the entire write block (header detect,
                    # maybe migrate, append) under a single POSIX flock
                    # so concurrent writers cannot append rows that a
                    # parallel migration's os.replace then silently
                    # deletes. The lock blocks (LOCK_EX) rather than
                    # falling back, so contenders wait and then see
                    # the post-migration header.
                    with _WriteLock(output_cost_path):
                        file_exists = os.path.isfile(output_cost_path)
                        file_has_content = file_exists and os.path.getsize(output_cost_path) > 0

                        fieldnames = new_fieldnames
                        if file_has_content:
                            with open(output_cost_path, 'r', encoding='utf-8') as f:
                                first_line = f.readline().strip()
                            if 'attempted_models' not in first_line:
                                # Oldest layout — no attempted_models, no job_id.
                                if job_id:
                                    _migrate_legacy_to_new_header(output_cost_path)
                                    # Re-read post-migration to confirm
                                    # the header is now new-format
                                    # (migration may have failed for
                                    # disk reasons).
                                    with open(output_cost_path, 'r', encoding='utf-8') as f:
                                        first_line = f.readline().strip()
                                if 'attempted_models' not in first_line:
                                    fieldnames = legacy_fieldnames
                                    del row['attempted_models']
                                    del row['job_id']
                                    abs_path = os.path.abspath(output_cost_path)
                                    if abs_path not in _legacy_csv_warned:
                                        _legacy_csv_warned.add(abs_path)
                                        rprint(
                                            "[yellow]Note: cost CSV "
                                            f"'{output_cost_path}' uses the legacy "
                                            "header; the new 'attempted_models' "
                                            "column will not be recorded. Delete or "
                                            "rename the file to start fresh with the "
                                            "attempted_models column.[/yellow]"
                                        )
                                elif 'job_id' not in first_line:
                                    fieldnames = mid_fieldnames
                                    del row['job_id']
                                # else: header has job_id → fall through to
                                # new_fieldnames write.
                            elif 'job_id' not in first_line:
                                # Mid-era layout — has attempted_models but
                                # no job_id. When PDD_JOB_ID is set (server-
                                # managed run that needs per-job isolation),
                                # migrate in place. When unset (CLI use),
                                # leave the file alone and write without
                                # job_id.
                                if job_id:
                                    _migrate_mid_to_new_header(output_cost_path)
                                    with open(output_cost_path, 'r', encoding='utf-8') as f:
                                        first_line = f.readline().strip()
                                if 'job_id' not in first_line:
                                    fieldnames = mid_fieldnames
                                    del row['job_id']

                        with open(output_cost_path, 'a', newline='', encoding='utf-8') as csvfile:
                            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
                            if not file_has_content:
                                writer.writeheader()
                            writer.writerow(row)

            except Exception as e:
                rprint(f"[red]Error tracking cost: {e}[/red]")

            # Always clear/restore `attempted_models` so it cannot leak into a
            # subsequent tracked command sharing the same ctx.obj.
            try:
                if ctx.obj is not None and isinstance(ctx.obj, dict):
                    if had_prior_attempted_models:
                        ctx.obj['attempted_models'] = prior_attempted_models
                    else:
                        ctx.obj.pop('attempted_models', None)
            except Exception:
                pass

        if exception_raised is not None:
            raise exception_raised

        return result

    return wrapper

def extract_cost_and_model(result: Any) -> Tuple[Any, str]:
    if isinstance(result, tuple) and len(result) >= 3:
        return result[-2], result[-1]
    return '', ''

def collect_files(args, kwargs) -> Tuple[List[str], List[str]]:
    input_files: List[str] = []
    output_files: List[str] = []

    input_param_names = {
        'prompt_file', 'prompt', 'input', 'input_file', 'source', 'source_file',
        'file', 'path', 'original_prompt_file_path', 'files', 'core_file',
        'code_file', 'unit_test_file', 'error_file', 'test_file', 'example_file'
    }

    output_param_names = {
        'output', 'output_file', 'output_path', 'destination', 'dest', 'target',
        'output_test', 'output_code', 'output_results'
    }

    for k, v in kwargs.items():
        if k in ('ctx', 'context', 'output_cost'):
            continue

        is_input_param = k in input_param_names or 'file' in k.lower() or 'prompt' in k.lower()
        is_output_param = k in output_param_names or 'output' in k.lower()

        if isinstance(v, str) and v:
            if is_input_param or is_output_param or looks_like_file(v):
                if is_output_param:
                    output_files.append(v)
                elif is_input_param:
                    input_files.append(v)
                else:
                    input_files.append(v)
        elif isinstance(v, list):
            for item in v:
                if isinstance(item, str) and item:
                    if is_input_param or is_output_param or looks_like_file(item):
                        if is_output_param:
                            output_files.append(item)
                        elif is_input_param:
                            input_files.append(item)
                        else:
                            input_files.append(item)

    for i, arg in enumerate(args):
        if i == 0 and hasattr(arg, 'obj'):
            continue

        if isinstance(arg, str) and arg and looks_like_file(arg):
            input_files.append(arg)
        elif isinstance(arg, list):
            for item in arg:
                if isinstance(item, str) and item and looks_like_file(item):
                    input_files.append(item)

    return input_files, output_files
