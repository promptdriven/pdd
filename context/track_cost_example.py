"""
Example demonstrating how to use the ``track_cost`` decorator from pdd.track_cost.

``track_cost`` is a Click command decorator. It wraps a Click command function so
that every invocation appends a row to a CSV file containing:

    timestamp, model, command, cost, input_files, output_files, attempted_models

Inputs:
    func (Callable): the Click command being wrapped.

Outputs:
    Callable: a wrapper that forwards the command's return value unchanged.
    Side effect: a CSV row appended to the path configured via
    ``ctx.obj['output_cost']`` (preferred) or the ``PDD_OUTPUT_COST_PATH``
    environment variable.

The decorator skips CSV writing entirely when ``PYTEST_CURRENT_TEST`` is set,
so this example clears that env var to demonstrate the real behavior.
"""
import os
import sys
import csv
import tempfile

# Make ``pdd.track_cost`` importable regardless of the working directory.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

import click  # noqa: E402
from click.testing import CliRunner  # noqa: E402

from pdd.track_cost import track_cost  # noqa: E402


# When running under pytest, track_cost intentionally skips CSV writing.
# Clear that env var so this standalone example actually writes the CSV.
os.environ.pop("PYTEST_CURRENT_TEST", None)


@click.group()
@click.option(
    "--output-cost",
    type=click.Path(),
    help="Enable cost tracking and write a CSV with usage details.",
)
@click.pass_context
def cli(ctx, output_cost):
    """Demo CLI for the track_cost decorator."""
    ctx.ensure_object(dict)
    ctx.obj["output_cost"] = output_cost


@cli.command()
@click.option("--prompt-file", type=click.Path(exists=True), required=True)
@click.option("--output", type=click.Path(), required=False)
@click.pass_context
@track_cost
def generate(ctx, prompt_file, output):
    """Legacy result shape: returns (output, cost, model_name).

    Returns:
        Tuple[str, float, str]: (output text, cost in USD, model name).
    """
    with open(prompt_file, "r", encoding="utf-8") as fh:
        prompt = fh.read()
    generated = f"Processed prompt: {prompt[:40]}"
    if output:
        with open(output, "w", encoding="utf-8") as out_fh:
            out_fh.write(generated)
    # Legacy result shape: (..., cost, model_name).
    return generated, 0.05, "gpt-4"


@cli.command()
@click.option("--prompt-file", type=click.Path(exists=True), required=True)
@click.option("--output", type=click.Path(), required=False)
@click.pass_context
@track_cost
def generate_enriched(ctx, prompt_file, output):
    """Enriched result shape: last element is a dict.

    The dict contains ``cost``, ``model_name`` and ``attempted_models`` so
    track_cost can record the full fallback chain.

    Returns:
        Tuple[str, dict]: (output text, metadata dict).
    """
    with open(prompt_file, "r", encoding="utf-8") as fh:
        prompt = fh.read()
    generated = f"Processed (enriched): {prompt[:40]}"
    if output:
        with open(output, "w", encoding="utf-8") as out_fh:
            out_fh.write(generated)
    metadata = {
        "cost": 0.12,
        "model_name": "claude-sonnet",
        # First attempt failed, then we fell back to claude-sonnet.
        "attempted_models": ["claude-opus", "claude-sonnet"],
    }
    return generated, metadata


def _print_csv(path):
    print(f"CSV file: {path}")
    print("Contents:")
    with open(path, "r", encoding="utf-8") as fh:
        reader = csv.reader(fh)
        for row in reader:
            print("  " + ",".join(row))


def main():
    # Work in an isolated temp directory so the example never writes into the
    # project tree and is fully reproducible.
    workdir = tempfile.mkdtemp(prefix="track_cost_example_")
    prompt_path = os.path.join(workdir, "prompt.txt")
    output_path = os.path.join(workdir, "output.txt")
    cost_csv = os.path.join(workdir, "cost.csv")

    with open(prompt_path, "w", encoding="utf-8") as fh:
        fh.write("Write a haiku about Python.")

    runner = CliRunner()

    print("=== Invocation 1: legacy result shape ===")
    result1 = runner.invoke(
        cli,
        [
            "--output-cost", cost_csv,
            "generate",
            "--prompt-file", prompt_path,
            "--output", output_path,
        ],
        catch_exceptions=False,
    )
    print(f"exit_code={result1.exit_code}")

    print()
    print("=== Invocation 2: enriched result shape with attempted_models ===")
    result2 = runner.invoke(
        cli,
        [
            "--output-cost", cost_csv,
            "generate-enriched",
            "--prompt-file", prompt_path,
            "--output", output_path,
        ],
        catch_exceptions=False,
    )
    print(f"exit_code={result2.exit_code}")

    print()
    _print_csv(cost_csv)

    print()
    print("Done. Notice:")
    print("  - Columns are in the order: "
          "timestamp, model, command, cost, input_files, output_files, attempted_models")
    print("  - Row 1 has an empty attempted_models cell (legacy shape).")
    print("  - Row 2 records the fallback chain 'claude-opus;claude-sonnet'.")


if __name__ == "__main__":
    main()
