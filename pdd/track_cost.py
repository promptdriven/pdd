import functools
from datetime import datetime
import csv
import os
from typing import Any, Callable, List, Optional, Tuple

import click
from rich import print as rprint


# Tracks cost-CSV paths we've already warned the user about for legacy headers.
# Keyed on absolute path so a long-running session does not repeat the notice.
_legacy_csv_warned: set = set()


def looks_like_file(path_str) -> bool:
    """Check if a string is path-like enough to consider for tracking."""
    if not isinstance(path_str, str) or not path_str.strip():
        return False
    return (
        bool(os.path.splitext(path_str)[1])
        or '/' in path_str
        or '\\' in path_str
        or os.path.isfile(path_str)
    )


def extract_cost_and_model(result: Any) -> Tuple[Any, str]:
    if isinstance(result, (tuple, list)) and len(result) >= 2:
        return result[-2], str(result[-1])
    return 0.0, "unknown"


def _coerce_token_count(value: Any) -> Optional[int]:
    if value is None or isinstance(value, bool):
        return None
    try:
        token_count = int(value)
    except (TypeError, ValueError):
        return None
    if token_count < 0:
        return None
    return token_count


def _direct_token_pair(payload: Any) -> Tuple[Optional[int], Optional[int]]:
    if isinstance(payload, dict):
        return (
            _coerce_token_count(payload.get('input_tokens')),
            _coerce_token_count(payload.get('output_tokens')),
        )
    return (
        _coerce_token_count(getattr(payload, 'input_tokens', None)),
        _coerce_token_count(getattr(payload, 'output_tokens', None)),
    )


def extract_token_counts(result: Any) -> Tuple[Optional[int], Optional[int]]:
    """Extract input/output token counts from supported result payloads."""
    seen: set[int] = set()

    def _scan(value: Any) -> Tuple[Optional[int], Optional[int]]:
        if value is None or isinstance(value, (str, bytes, int, float, bool)):
            return None, None

        value_id = id(value)
        if value_id in seen:
            return None, None
        seen.add(value_id)

        input_tokens, output_tokens = _direct_token_pair(value)
        if input_tokens is not None or output_tokens is not None:
            return input_tokens, output_tokens

        children: List[Any] = []
        if isinstance(value, dict):
            for key in ('usage', 'tokens', 'token_usage', 'metadata', 'response'):
                if key in value:
                    children.append(value[key])
            children.extend(value.values())
        elif isinstance(value, (tuple, list)):
            children.extend(value[:-2] if isinstance(value, tuple) and len(value) >= 3 else value)
        else:
            for attr in ('usage', 'tokens', 'token_usage', 'metadata', 'response'):
                if hasattr(value, attr):
                    children.append(getattr(value, attr))

        found_input = None
        found_output = None
        for child in children:
            child_input, child_output = _scan(child)
            if found_input is None and child_input is not None:
                found_input = child_input
            if found_output is None and child_output is not None:
                found_output = child_output
            if found_input is not None and found_output is not None:
                break
        return found_input, found_output

    return _scan(result)


def collect_files(args, kwargs) -> Tuple[List[str], List[str]]:
    input_files: List[str] = []
    output_files: List[str] = []

    for key, value in kwargs.items():
        if key in ('ctx', 'context', 'output_cost', 'output_cost_path'):
            continue

        values = value if isinstance(value, (list, tuple)) else [value]
        for item in values:
            if not isinstance(item, str) or not item:
                continue
            if key.startswith('output'):
                output_files.append(item)
            elif os.path.isfile(item):
                input_files.append(item)

    for index, arg in enumerate(args):
        if index == 0 and hasattr(arg, 'obj'):
            continue

        values = arg if isinstance(arg, (list, tuple)) else [arg]
        for item in values:
            if isinstance(item, str) and item and os.path.isfile(item):
                input_files.append(item)

    return input_files, output_files


def _get_output_cost_path(ctx) -> Optional[str]:
    if ctx is not None and ctx.obj is not None and hasattr(ctx.obj, 'get'):
        return (
            ctx.obj.get('output_cost')
            or ctx.obj.get('output_cost_path')
            or ctx.obj.get('PDD_OUTPUT_COST_PATH')
            or os.environ.get('PDD_OUTPUT_COST_PATH')
        )
    return os.environ.get('PDD_OUTPUT_COST_PATH')


def _new_fieldnames() -> List[str]:
    return [
        'timestamp',
        'model',
        'command',
        'cost',
        'input_tokens',
        'output_tokens',
        'input_files',
        'output_files',
        'attempted_models',
    ]


def _fieldnames_for_path(output_cost_path: str) -> Tuple[List[str], bool]:
    fieldnames = _new_fieldnames()
    file_exists = os.path.isfile(output_cost_path)
    file_has_content = file_exists and os.path.getsize(output_cost_path) > 0

    if file_has_content:
        with open(output_cost_path, 'r', encoding='utf-8') as cost_file:
            first_line = cost_file.readline()
        parsed_header = next(csv.reader([first_line]), [])
        fieldnames = parsed_header or fieldnames

    return fieldnames, file_has_content


def _warn_if_legacy(output_cost_path: str, fieldnames: List[str]) -> None:
    missing_columns = [
        column for column in ('input_tokens', 'output_tokens', 'attempted_models')
        if column not in fieldnames
    ]
    if not missing_columns:
        return

    abs_path = os.path.abspath(output_cost_path)
    if abs_path in _legacy_csv_warned:
        return

    _legacy_csv_warned.add(abs_path)
    missing = ', '.join(missing_columns)
    rprint(
        "[yellow]Note: cost CSV "
        f"'{output_cost_path}' uses a legacy header; the new column(s) "
        f"{missing} will not be recorded. Delete or rename the file to opt in."
        "[/yellow]"
    )


def _attempted_models(ctx, model_name: str) -> str:
    attempted = None
    if ctx is not None and isinstance(ctx.obj, dict):
        attempted = ctx.obj.get('attempted_models')
    if not attempted:
        attempted = [model_name]
    return ';'.join(str(model).replace(';', ':') for model in attempted)


def _record_core_dump_files(ctx, input_files: List[str], output_files: List[str]) -> None:
    if ctx is None or ctx.obj is None or not hasattr(ctx.obj, 'get'):
        return
    if not ctx.obj.get('core_dump'):
        return

    files_set = ctx.obj.get('core_dump_files', set())
    for path in input_files + output_files:
        if isinstance(path, str) and path:
            files_set.add(os.path.abspath(path))
    ctx.obj['core_dump_files'] = files_set


def _clear_attempted_models(ctx) -> Tuple[bool, Any]:
    if ctx is not None and isinstance(ctx.obj, dict) and 'attempted_models' in ctx.obj:
        return True, ctx.obj.pop('attempted_models')
    return False, None


def _restore_attempted_models(ctx, had_prior: bool, prior_value: Any) -> None:
    if ctx is None or not isinstance(ctx.obj, dict):
        return
    if had_prior:
        ctx.obj['attempted_models'] = prior_value
    else:
        ctx.obj.pop('attempted_models', None)


def track_cost(func):
    @functools.wraps(func)
    def wrapper(*args, **kwargs):
        try:
            ctx = click.get_current_context(silent=True)
        except Exception:
            ctx = None

        start_time = datetime.now()
        had_prior_attempted, prior_attempted = _clear_attempted_models(ctx)
        result = None
        command_error = None

        try:
            result = func(*args, **kwargs)
        except Exception as exc:
            command_error = exc
        finally:
            end_time = datetime.now()
            del end_time

            try:
                input_files, output_files = collect_files(args, kwargs)
                _record_core_dump_files(ctx, input_files, output_files)

                output_cost_path = _get_output_cost_path(ctx)
                if (
                    ctx is not None
                    and command_error is None
                    and output_cost_path
                    and os.environ.get('PYTEST_CURRENT_TEST') is None
                ):
                    cost, model_name = extract_cost_and_model(result)
                    input_tokens, output_tokens = extract_token_counts(result)
                    attempted_models = _attempted_models(ctx, model_name)

                    row = {
                        'timestamp': start_time.strftime('%Y-%m-%dT%H:%M:%S.%f')[:-3],
                        'model': model_name,
                        'command': ctx.command.name if ctx.command else 'unknown',
                        'cost': cost,
                        'input_tokens': input_tokens if input_tokens is not None else '',
                        'output_tokens': output_tokens if output_tokens is not None else '',
                        'input_files': ';'.join(input_files),
                        'output_files': ';'.join(output_files),
                        'attempted_models': attempted_models,
                    }

                    fieldnames, file_has_content = _fieldnames_for_path(output_cost_path)
                    if file_has_content:
                        _warn_if_legacy(output_cost_path, fieldnames)

                    with open(output_cost_path, 'a', newline='', encoding='utf-8') as csvfile:
                        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
                        if not file_has_content:
                            writer.writeheader()
                        writer.writerow({field: row.get(field, '') for field in fieldnames})

            except Exception as exc:
                rprint(f"[red]Error tracking cost: {exc}[/red]")
            finally:
                _restore_attempted_models(ctx, had_prior_attempted, prior_attempted)

        if command_error is not None:
            raise command_error

        return result

    return wrapper
