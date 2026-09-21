import functools
from datetime import datetime
from importlib import metadata
import csv
import os
import click
from rich import print as rprint
from typing import Any, List, Tuple

# Tracks cost-CSV paths we've already warned the user about for the
# "legacy header, attempted_models column will be omitted" case. Keyed on
# absolute path so a long-running session doesn't spam the same notice.
_legacy_csv_warned: set = set()

_LEGACY_FIELDNAMES = ['timestamp', 'model', 'command', 'cost', 'input_files', 'output_files']
_ATTEMPT_FIELDNAMES = _LEGACY_FIELDNAMES + ['attempted_models']
_PROVENANCE_FIELDNAMES = [
    'requested_model',
    'resolved_model',
    'model_selection_outcome',
    'strength_used',
    'cli_version',
    'deepswe_manifest_date',
]
_FULL_FIELDNAMES = _ATTEMPT_FIELDNAMES + _PROVENANCE_FIELDNAMES

# ctx.obj key under which a tracked command may stash its
# `(str(result), total_cost, model_name)` tuple right before raising an
# intentional `click.exceptions.Exit` (e.g. `pdd sync` exiting 1 when the
# aggregated result has overall_success == False, issue #1979). The wrapper
# below writes the cost-CSV row from this stash so a failed-but-completed run
# keeps its row — the agentic runner parses PDD_OUTPUT_COST_PATH from child
# syncs to accumulate cost and enforce --budget. Crashes and other exceptions
# still skip the row as before.
EXIT_COST_RESULT_KEY = 'track_cost_exit_result'


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

        start_time = datetime.now()
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
            end_time = datetime.now()

            # Pop any stashed exit-result unconditionally so it can never leak
            # into a later tracked command sharing the same ctx.obj. It only
            # feeds the row when the command raised an intentional click Exit.
            stashed_exit_result = None
            try:
                if ctx.obj is not None and isinstance(ctx.obj, dict):
                    stashed_exit_result = ctx.obj.pop(EXIT_COST_RESULT_KEY, None)
            except Exception:
                stashed_exit_result = None
            exit_result = (
                stashed_exit_result
                if isinstance(exception_raised, click.exceptions.Exit)
                else None
            )

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

                if exception_raised is None or exit_result is not None:
                    if ctx.obj and hasattr(ctx.obj, 'get'):
                        output_cost_path = ctx.obj.get('output_cost') or os.getenv('PDD_OUTPUT_COST_PATH')
                    else:
                        output_cost_path = os.getenv('PDD_OUTPUT_COST_PATH')

                    if output_cost_path and os.environ.get('PYTEST_CURRENT_TEST') is None:
                        command_name = ctx.command.name
                        cost, model_name = extract_cost_and_model(
                            result if exception_raised is None else exit_result
                        )

                        attempted_models_list = ctx.obj.get('attempted_models') if ctx.obj and isinstance(ctx.obj, dict) else None
                        if not attempted_models_list:
                            attempted_models_list = [model_name]
                        attempted_models = ';'.join(str(m).replace(';', ':') for m in attempted_models_list)

                        timestamp = start_time.strftime('%Y-%m-%dT%H:%M:%S.%f')[:-3]

                        try:
                            cli_version = metadata.version('pdd')
                        except metadata.PackageNotFoundError:
                            cli_version = ''

                        row = {
                            'timestamp': timestamp,
                            'model': model_name,
                            'command': command_name,
                            'cost': cost,
                            'input_files': ';'.join(input_files),
                            'output_files': ';'.join(output_files),
                            'attempted_models': attempted_models,
                            'requested_model': ctx.obj.get('requested_model', '') if ctx.obj and isinstance(ctx.obj, dict) else '',
                            'resolved_model': ctx.obj.get('resolved_model', '') if ctx.obj and isinstance(ctx.obj, dict) else '',
                            'model_selection_outcome': ctx.obj.get('model_selection_outcome', '') if ctx.obj and isinstance(ctx.obj, dict) else '',
                            'strength_used': ctx.obj.get('strength_used', '') if ctx.obj and isinstance(ctx.obj, dict) else '',
                            'cli_version': cli_version,
                            'deepswe_manifest_date': ctx.obj.get('deepswe_manifest_date', '') if ctx.obj and isinstance(ctx.obj, dict) else '',
                        }

                        file_exists = os.path.isfile(output_cost_path)
                        file_has_content = file_exists and os.path.getsize(output_cost_path) > 0

                        fieldnames = _FULL_FIELDNAMES
                        if file_has_content:
                            with open(output_cost_path, 'r', encoding='utf-8') as f:
                                first_line = f.readline().strip()
                                header = [part.strip() for part in first_line.split(',') if part.strip()]
                                if 'attempted_models' not in header:
                                    fieldnames = _LEGACY_FIELDNAMES
                                    for extra in ['attempted_models'] + _PROVENANCE_FIELDNAMES:
                                        row.pop(extra, None)
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
                                elif 'deepswe_manifest_date' not in header:
                                    # Mid-generation legacy file: keep the
                                    # existing header stable and write only the
                                    # columns the file already declares.
                                    fieldnames = _ATTEMPT_FIELDNAMES
                                    for extra in _PROVENANCE_FIELDNAMES:
                                        row.pop(extra, None)

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
