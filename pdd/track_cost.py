import functools
from datetime import datetime
import csv
import os
import click
from rich import print as rprint

def track_cost(func):
    """
    Decorator to track the cost of command execution in the "pdd" CLI program.
    
    It logs the execution details into a CSV file specified by the user or
    through the PDD_OUTPUT_COST_PATH environment variable.
    """
    @functools.wraps(func)
    def wrapper(*args, **kwargs):
        ctx = click.get_current_context()
        if ctx is None:
            return func(*args, **kwargs)

        start_time = datetime.now()
        try:
            # Execute the original command function
            result = func(*args, **kwargs)
        except Exception as e:
            # Let any exceptions from the command propagate
            raise e
        end_time = datetime.now()

        try:
            # Step 5: Retrieve Output Cost Option
            output_cost_path = (
                ctx.params.get('output_cost') or
                os.getenv('PDD_OUTPUT_COST_PATH')
            )
            
            if not output_cost_path:
                # If no output cost path is specified, skip logging
                return result

            # Step 6: Prepare Cost Data

            # Determine the command name
            command_name = ctx.command.name

            # Extract cost and model name from the result tuple
            # Assuming the second to last element is cost and the last is model name
            if isinstance(result, tuple) and len(result) >= 3:
                cost = result[-2]
                model_name = result[-1]
            else:
                cost = ''
                model_name = ''

            # Collect input and output file paths from command arguments
            input_files = []
            output_files = []

            for param, value in ctx.params.items():
                if isinstance(value, str):
                    if 'output' not in param.lower() and param != 'output_cost':
                        input_files.append(value)
                    elif 'output' in param.lower() and param != 'output_cost':
                        output_files.append(value)
                elif isinstance(value, (list, tuple)):
                    # Handle multiple input/output files
                    for item in value:
                        if isinstance(item, str):
                            if 'input' in param.lower():
                                input_files.append(item)
                            elif 'output' in param.lower() and param != 'output_cost':
                                output_files.append(item)

            # Format the timestamp
            timestamp = start_time.isoformat()

            # Prepare the CSV row
            row = {
                'timestamp': timestamp,
                'model': model_name,
                'command': command_name,
                'cost': cost,
                'input_files': ';'.join(input_files),
                'output_files': ';'.join(output_files),
            }

            # Step 7: Append Cost Data to CSV File

            # Check if the CSV file exists to determine if header is needed
            file_exists = os.path.isfile(output_cost_path)

            # Define the CSV headers
            fieldnames = ['timestamp', 'model', 'command', 'cost', 'input_files', 'output_files']

            # Open the CSV file in append mode
            with open(output_cost_path, 'a', newline='', encoding='utf-8') as csvfile:
                writer = csv.DictWriter(csvfile, fieldnames=fieldnames)

                # Write header if the file is new
                if not file_exists:
                    writer.writeheader()

                # Write the cost data row
                writer.writerow(row)

        except Exception as e:
            # Step 8: Handle Exceptions Gracefully
            rprint(f"[red]Error tracking cost: {e}[/red]")

        # Step 9: Return the Command Result
        return result

    return wrapper
