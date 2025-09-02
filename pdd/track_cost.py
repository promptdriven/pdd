import functools
from datetime import datetime
import csv
import os
import click
from rich import print as rprint
from typing import Any, Tuple

def track_cost(func):
    @functools.wraps(func)
    def wrapper(*args, **kwargs):
        ctx = click.get_current_context()
        if ctx is None:
            return func(*args, **kwargs)

        start_time = datetime.now()
        try:
            result = func(*args, **kwargs)
        except Exception as e:
            raise e
        end_time = datetime.now()

        try:
            if ctx.obj and hasattr(ctx.obj, 'get'):
                output_cost_path = ctx.obj.get('output_cost') or os.getenv('PDD_OUTPUT_COST_PATH')
            else:
                output_cost_path = os.getenv('PDD_OUTPUT_COST_PATH')
            
            if not output_cost_path:
                return result

            command_name = ctx.command.name

            cost, model_name = extract_cost_and_model(result)

            input_files, output_files = collect_files(args, kwargs)

            timestamp = start_time.strftime('%Y-%m-%dT%H:%M:%S.%f')[:-3]

            row = {
                'timestamp': timestamp,
                'model': model_name,
                'command': command_name,
                'cost': cost,
                'input_files': ';'.join(input_files),
                'output_files': ';'.join(output_files),
            }

            file_exists = os.path.isfile(output_cost_path)
            fieldnames = ['timestamp', 'model', 'command', 'cost', 'input_files', 'output_files']

            with open(output_cost_path, 'a', newline='', encoding='utf-8') as csvfile:
                writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
                if not file_exists:
                    writer.writeheader()
                writer.writerow(row)

            print(f"Debug: Writing row to CSV: {row}")
            print(f"Debug: Input files: {input_files}")
            print(f"Debug: Output files: {output_files}")

        except Exception as e:
            rprint(f"[red]Error tracking cost: {e}[/red]")

        return result

    return wrapper

def extract_cost_and_model(result: Any) -> Tuple[Any, str]:
    if isinstance(result, tuple) and len(result) >= 3:
        return result[-2], result[-1]
    return '', ''

def collect_files(args, kwargs):
    input_files = []
    output_files = []

    # Collect from args
    for arg in args:
        if isinstance(arg, str):
            input_files.append(arg)
        elif isinstance(arg, list):
            input_files.extend([f for f in arg if isinstance(f, str)])

    # Collect from kwargs
    for k, v in kwargs.items():
        if k == 'output_cost':
            continue
        if isinstance(v, str):
            if k.startswith('output'):
                output_files.append(v)
            else:
                input_files.append(v)
        elif isinstance(v, list):
            if k.startswith('output'):
                output_files.extend([f for f in v if isinstance(f, str)])
            else:
                input_files.extend([f for f in v if isinstance(f, str)])

    print(f"Debug: Collected input files: {input_files}")
    print(f"Debug: Collected output files: {output_files}")
    return input_files, output_files
