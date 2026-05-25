"""
Demonstrates the usage of ``context_generator_main`` from
``pdd.context_generator_main``.

Inputs to ``context_generator_main``:
    - ctx (click.Context): Click context whose ``ctx.obj`` dict holds the
      global options (strength, temperature, time, verbose, quiet, force,
      local, context, confirm_callback).
    - prompt_file (str): Path to the .prompt file used to generate the
      original code.
    - code_file (str): Path to the existing source code file.
    - output (Optional[str]): Path to save the generated example. If
      ``None``, ``construct_paths`` picks a default location.
    - format (Optional[str]): ``"code"``, ``"md"``, or ``None``. When
      ``None`` the user-supplied ``output`` extension is honored verbatim
      (issue #1148 fix).

Outputs of ``context_generator_main`` (Tuple[str, float, str]):
    - generated_code (str): The resulting example code.
    - total_cost (float): The cost of the LLM operation in USD.
    - model_name (str): The name of the model that performed the
      generation.

This example mocks ``construct_paths``, ``context_generator``, and
``CloudConfig.get_jwt_token`` so it runs offline with no API keys.
"""

import os
import sys
from pathlib import Path
from unittest.mock import patch

# Make the in-repo ``pdd`` package importable regardless of CWD.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

import click  # noqa: E402

from pdd.context_generator_main import context_generator_main  # noqa: E402


def run_example() -> None:
    # 1) Lay out a small workspace under ``./output``.
    output_dir = Path(os.path.dirname(__file__)) / "output_example"
    output_dir.mkdir(exist_ok=True)

    prompt_path = output_dir / "math_utils_python.prompt"
    code_path = output_dir / "math_utils.py"
    example_output_path = output_dir / "math_utils_example.py"

    prompt_path.write_text(
        "Task: Create a utility for basic math operations.\n"
        "Include a function 'add(a, b)' that returns the sum.",
        encoding="utf-8",
    )
    code_path.write_text("def add(a, b):\n    return a + b\n", encoding="utf-8")

    # 2) Build a real Click context with the same ``obj`` keys the CLI
    #    group populates. ``local=True`` forces local execution so the
    #    cloud path is never touched.
    ctx = click.Context(click.Command("example"))
    ctx.obj = {
        "verbose": False,
        "strength": 0.5,
        "temperature": 0.0,
        "time": None,
        "force": True,
        "quiet": True,
        "local": True,
        "context": None,
        "confirm_callback": None,
    }

    # 3) Mock the heavy dependencies so the example is fully offline.
    fake_example_code = (
        '"""Example: how to use math_utils.add."""\n'
        "from math_utils import add\n"
        "\n"
        "print(add(2, 3))\n"
    )

    with patch("pdd.context_generator_main.construct_paths") as mock_paths, patch(
        "pdd.context_generator_main.context_generator"
    ) as mock_gen:
        mock_paths.return_value = (
            {},  # resolved_config
            {
                "prompt_file": prompt_path.read_text(encoding="utf-8"),
                "code_file": code_path.read_text(encoding="utf-8"),
            },
            {"output": str(example_output_path)},
            "python",
        )
        mock_gen.return_value = (fake_example_code, 0.001234, "fake-model")

        generated_code, cost, model = context_generator_main(
            ctx=ctx,
            prompt_file=str(prompt_path),
            code_file=str(code_path),
            output=str(example_output_path),
            format=None,
        )

    # 4) Report results.
    print("--- context_generator_main results ---")
    print(f"Model:  {model}")
    print(f"Cost:   ${cost:.6f}")
    print(f"Saved:  {example_output_path}")
    print()
    print("--- Generated code ---")
    print(generated_code)


if __name__ == "__main__":
    run_example()
