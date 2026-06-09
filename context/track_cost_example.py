"""Example showing how to use the `track_cost` decorator from `pdd.track_cost`.

The decorator wraps a Click command function, records the per-command cost,
the model that succeeded, and the audit log of attempted models, then appends
a row to the CSV file specified via `--output-cost` (or the
`PDD_OUTPUT_COST_PATH` environment variable).

Each CSV row contains:
    - timestamp:        ISO-8601 datetime of when the command started
    - model:            successful model name (string)
    - command:          Click command name (string)
    - cost:             cost in USD (float, e.g. 0.05 means $0.05)
    - input_tokens:     prompt token count (integer, blank when unavailable)
    - output_tokens:    completion token count (integer, blank when unavailable)
    - input_files:      semicolon-separated input file paths
    - output_files:     semicolon-separated output file paths
    - attempted_models: semicolon-separated audit log of models tried
                        (e.g. "vertex_ai/gemini-2.5-pro;deepseek/deepseek-chat").
                        Sequential paths emit wall-clock attempt order;
                        concurrent paths (e.g. auto-deps --concurrency > 1)
                        sort by file-submission index for deterministic
                        output across runs.
"""

import csv
import os
import sys
import tempfile

# Ensure `pdd.track_cost` resolves no matter where this script is launched from.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

import click  # noqa: E402
from typing import Any, Dict, Optional, Tuple  # noqa: E402

from pdd.track_cost import track_cost  # noqa: E402


@click.group()
@click.option(
    '--output-cost',
    type=click.Path(),
    help='Path to a CSV file where per-command cost rows will be appended.',
)
@click.pass_context
def cli(ctx, output_cost):
    """Tiny demo CLI that stores output_cost as a CSV path string in ctx.obj."""
    ctx.ensure_object(dict)
    ctx.obj['output_cost'] = output_cost


@cli.command()
@click.option('--prompt-file', type=click.Path(exists=True), required=True,
              help='Path to a prompt file (input).')
@click.option('--output', type=click.Path(), required=False,
              help='Path to write generated output (output).')
@click.pass_context
@track_cost
def generate(ctx, prompt_file: str, output: Optional[str]) -> Tuple[Dict[str, Any], float, str]:
    """Pretend to run an LLM and return (payload, cost_usd, model_name).

    Args:
        ctx: Click context containing the output cost CSV path and attempt log.
        prompt_file: Existing prompt file path used as the command input.
        output: Optional generated output file path written by this command.

    Returns:
        Tuple of (payload, cost_in_dollars, successful_model_name). The payload
        contains token counts in tokens. track_cost extracts cost from index
        [-2], model from index [-1], and token counts from the payload.
    """
    with open(prompt_file, 'r', encoding='utf-8') as fh:
        prompt = fh.read()

    # Simulate what `llm_invoke` does during command execution when it tries
    # multiple models in order (the first attempt failed -> fallback succeeded).
    # This list is published on `ctx.obj` *during* the command, mirroring how
    # `llm_invoke` records each candidate, and becomes the `attempted_models`
    # column. track_cost scopes this per-command, so populating it here (not in
    # the group callback) reflects real runtime behavior.
    ctx.obj['attempted_models'] = [
        'vertex_ai/gemini-2.5-pro',
        'deepseek/deepseek-chat',
    ]

    generated = f"Processed prompt ({len(prompt)} chars)"
    if output:
        with open(output, 'w', encoding='utf-8') as fh:
            fh.write(generated)

    payload = {
        'output': generated,
        'usage': {
            'input_tokens': len(prompt.split()),
            'output_tokens': len(generated.split()),
        },
    }

    # cost: $0.05 USD, model: the one that eventually succeeded
    return payload, 0.05, 'deepseek/deepseek-chat'


def _print_csv(cost_path: str) -> None:
    print('--- contents of cost CSV ---')
    with open(cost_path, 'r', encoding='utf-8') as fh:
        sys.stdout.write(fh.read())
    print('--- end of cost CSV ---')


def main() -> int:
    # Use a temp directory so we never pollute the user's working directory.
    with tempfile.TemporaryDirectory() as tmpdir:
        prompt_path = os.path.join(tmpdir, 'demo.prompt')
        output_path = os.path.join(tmpdir, 'demo.out')
        cost_path = os.path.join(tmpdir, 'cost.csv')

        with open(prompt_path, 'w', encoding='utf-8') as fh:
            fh.write('Hello, world!')

        # IMPORTANT: track_cost skips CSV writes when PYTEST_CURRENT_TEST is set.
        # Make sure it is NOT set when running the example standalone.
        os.environ.pop('PYTEST_CURRENT_TEST', None)

        # Invoke the Click CLI in-process via standalone_mode=False so we can
        # inspect the resulting CSV here.
        cli(
            [
                '--output-cost', cost_path,
                'generate',
                '--prompt-file', prompt_path,
                '--output', output_path,
            ],
            standalone_mode=False,
        )

        _print_csv(cost_path)

        # The last column must be attempted_models — newest column.
        with open(cost_path, 'r', encoding='utf-8') as fh:
            reader = csv.reader(fh)
            rows = list(reader)
        assert len(rows) >= 2, f'expected header + at least 1 data row, got {rows}'
        header = rows[0]
        data_row = rows[1]
        assert header[-1] == 'attempted_models', f'expected attempted_models last, got {header}'
        print('attempted_models column is last:', header[-1] == 'attempted_models')
        assert header[4:6] == ['input_tokens', 'output_tokens'], header
        print('token columns are present:', header[4:6])

        # Verify the full fallback history made it into the CSV row, proving the
        # per-command scoping in track_cost preserves `attempted_models` written
        # during the wrapped command's execution.
        expected_attempted = 'vertex_ai/gemini-2.5-pro;deepseek/deepseek-chat'
        actual_attempted = data_row[-1]
        assert actual_attempted == expected_attempted, (
            f'expected attempted_models cell {expected_attempted!r}, '
            f'got {actual_attempted!r}'
        )
        print('attempted_models cell records full fallback history:', actual_attempted)

    return 0


if __name__ == '__main__':
    sys.exit(main())
