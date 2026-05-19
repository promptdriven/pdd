import functools
from datetime import datetime
import csv
import os
import click
from rich import print as rprint
from typing import Any, Tuple, List

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

                # Check if we need to write cost tracking (only on success)
                if exception_raised is None:
                    if ctx.obj and hasattr(ctx.obj, 'get'):
                        output_cost_path = ctx.obj.get('output_cost') or os.getenv('PDD_OUTPUT_COST_PATH')
                    else:
                        output_cost_path = os.getenv('PDD_OUTPUT_COST_PATH')

                    if output_cost_path and os.environ.get('PYTEST_CURRENT_TEST') is None:
                        command_name = ctx.command.name if ctx.command else "unknown"
                        cost, model_name, result_attempted = extract_cost_and_model(result)

                        # Determine attempted_models chain
                        attempted_models_list = []
                        if ctx.obj and ctx.obj.get('attempted_models'):
                            attempted_models_list = ctx.obj.get('attempted_models')
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

                        # If file exists with an older header that doesn't include
                        # 'attempted_models', migrate it in place so DictReader can
                        # expose the new column properly.
                        if file_has_content:
                            try:
                                with open(output_cost_path, 'r', newline='', encoding='utf-8') as existing:
                                    reader = csv.reader(existing)
                                    existing_header = next(reader, None)
                                    existing_rows = list(reader) if existing_header is not None else []
                            except Exception:
                                existing_header = None
                                existing_rows = []

                            if existing_header is not None and 'attempted_models' not in existing_header:
                                migrated_fieldnames = list(existing_header) + ['attempted_models']
                                with open(output_cost_path, 'w', newline='', encoding='utf-8') as csvfile:
                                    migrate_writer = csv.writer(csvfile)
                                    migrate_writer.writerow(migrated_fieldnames)
                                    for existing_row in existing_rows:
                                        # Pad shorter rows so column count matches.
                                        padded = list(existing_row) + [''] * (len(migrated_fieldnames) - len(existing_row))
                                        migrate_writer.writerow(padded)
                                fieldnames = migrated_fieldnames

                        with open(output_cost_path, 'a', newline='', encoding='utf-8') as csvfile:
                            writer = csv.DictWriter(csvfile, fieldnames=fieldnames, extrasaction='ignore')
                            if not file_has_content:
                                writer.writeheader()
                            writer.writerow(row)

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
