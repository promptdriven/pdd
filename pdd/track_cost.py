import functools
from datetime import datetime
import csv
import os
import click
from rich import print as rprint
from typing import Any, List, Optional, Tuple

# Tracks cost-CSV paths we've already warned the user about for legacy headers.
# Keyed on absolute path so a long-running session doesn't spam the same notice.
_legacy_csv_warned: set = set()


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

                if exception_raised is None:
                    if ctx.obj and hasattr(ctx.obj, 'get'):
                        output_cost_path = ctx.obj.get('output_cost') or os.getenv('PDD_OUTPUT_COST_PATH')
                    else:
                        output_cost_path = os.getenv('PDD_OUTPUT_COST_PATH')

                    if output_cost_path and os.environ.get('PYTEST_CURRENT_TEST') is None:
                        command_name = ctx.command.name
                        cost, model_name = extract_cost_and_model(result)
                        input_tokens, output_tokens = extract_token_counts(result)

                        attempted_models_list = ctx.obj.get('attempted_models') if ctx.obj and isinstance(ctx.obj, dict) else None
                        if not attempted_models_list:
                            attempted_models_list = [model_name]
                        attempted_models = ';'.join(str(m).replace(';', ':') for m in attempted_models_list)

                        timestamp = start_time.strftime('%Y-%m-%dT%H:%M:%S.%f')[:-3]

                        row = {
                            'timestamp': timestamp,
                            'model': model_name,
                            'command': command_name,
                            'cost': cost,
                            'input_tokens': input_tokens if input_tokens is not None else '',
                            'output_tokens': output_tokens if output_tokens is not None else '',
                            'input_files': ';'.join(input_files),
                            'output_files': ';'.join(output_files),
                            'attempted_models': attempted_models,
                        }

                        file_exists = os.path.isfile(output_cost_path)
                        file_has_content = file_exists and os.path.getsize(output_cost_path) > 0

                        new_fieldnames = [
                            'timestamp', 'model', 'command', 'cost',
                            'input_tokens', 'output_tokens',
                            'input_files', 'output_files', 'attempted_models',
                        ]

                        fieldnames = new_fieldnames
                        if file_has_content:
                            with open(output_cost_path, 'r', encoding='utf-8') as f:
                                first_line = f.readline()
                                parsed_header = next(csv.reader([first_line]), [])
                                fieldnames = parsed_header or new_fieldnames
                                missing_new_columns = [
                                    column for column in (
                                        'input_tokens', 'output_tokens',
                                        'attempted_models',
                                    )
                                    if column not in fieldnames
                                ]
                                if missing_new_columns:
                                    abs_path = os.path.abspath(output_cost_path)
                                    if abs_path not in _legacy_csv_warned:
                                        _legacy_csv_warned.add(abs_path)
                                        missing = ', '.join(missing_new_columns)
                                        rprint(
                                            "[yellow]Note: cost CSV "
                                            f"'{output_cost_path}' uses the legacy "
                                            f"header; the new column(s) {missing} "
                                            "will not be recorded. Delete or "
                                            "rename the file to start fresh with the "
                                            "expanded columns.[/yellow]"
                                        )
                        row = {field: row.get(field, '') for field in fieldnames}

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


def _coerce_token_count(value: Any) -> Optional[int]:
    """Convert a token count to int when it is a valid non-negative number."""
    if value is None or isinstance(value, bool):
        return None
    try:
        token_count = int(value)
    except (TypeError, ValueError):
        return None
    if token_count < 0:
        return None
    return token_count


def _read_token_pair(payload: Any) -> Tuple[Optional[int], Optional[int]]:
    """Read direct input/output token keys or attributes from one object."""
    if isinstance(payload, dict):
        input_value = payload.get('input_tokens')
        output_value = payload.get('output_tokens')
        return _coerce_token_count(input_value), _coerce_token_count(output_value)

    input_value = getattr(payload, 'input_tokens', None)
    output_value = getattr(payload, 'output_tokens', None)
    return _coerce_token_count(input_value), _coerce_token_count(output_value)


def extract_token_counts(result: Any) -> Tuple[Optional[int], Optional[int]]:
    """Extract input/output token counts from result payloads when present."""
    seen: set[int] = set()

    def _scan(value: Any) -> Tuple[Optional[int], Optional[int]]:
        if value is None or isinstance(value, (str, bytes, int, float, bool)):
            return None, None

        value_id = id(value)
        if value_id in seen:
            return None, None
        seen.add(value_id)

        input_tokens, output_tokens = _read_token_pair(value)
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
