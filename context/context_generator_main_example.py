"""Example: how to invoke `context_generator_main` to generate example code.

This script demonstrates the CLI wrapper `context_generator_main` from
`pdd.context_generator_main`. It mocks the internal `context_generator`
dependency so the example runs without an LLM call or network access.

context_generator_main signature:
    (ctx: click.Context, prompt_file: str, code_file: str,
     output: Optional[str], format: Optional[str] = None) -> Tuple[str, float, str]

Inputs:
    - ctx: a click.Context. The wrapper reads keys from ctx.obj such as
      'strength' (float), 'temperature' (float), 'time' (float|None),
      'force' (bool), 'quiet' (bool), 'verbose' (bool), 'local' (bool),
      'context' (str|None), 'confirm_callback' (Callable|None).
    - prompt_file: filesystem path (str) to the .prompt file.
    - code_file:   filesystem path (str) to the source code file.
    - output: optional output path. If it has a non-empty suffix the
      wrapper writes to that exact path verbatim (.md/.yml/.py are all honored).
      If it has no suffix, the wrapper applies a format/language-driven extension.
    - format: optional 'code' or 'md'. None means use construct_paths default.

Returns:
    (generated_code: str, total_cost_usd: float, model_name: str)
"""

import os
import sys
from pathlib import Path
from unittest.mock import patch

import click

# Ensure the package can be imported regardless of cwd.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pdd.context_generator_main import context_generator_main  # noqa: E402


def build_ctx(local: bool = True, quiet: bool = False) -> click.Context:
    """Build a Click context with the keys the wrapper reads from ctx.obj."""
    ctx = click.Context(click.Command("example"))
    ctx.obj = {
        "verbose": False,
        "strength": 0.5,
        "temperature": 0.0,
        "time": None,
        "force": True,
        "quiet": quiet,
        "local": local,           # True => skip cloud entirely; no network or auth
        "context": None,
        "confirm_callback": None,
    }
    return ctx


def main() -> None:
    work_dir = Path(os.path.dirname(__file__)) / "_cgm_example_output"
    work_dir.mkdir(exist_ok=True)

    prompt_file = work_dir / "math_utils_python.prompt"
    code_file = work_dir / "math_utils.py"
    output_file = work_dir / "math_utils_example.py"

    prompt_file.write_text(
        "Task: Create a utility module with a function `add(a, b)` that returns a + b.",
        encoding="utf-8",
    )
    code_file.write_text(
        "def add(a, b):\n    return a + b\n",
        encoding="utf-8",
    )

    # The wrapper delegates to `construct_paths` (resolves config + reads files)
    # and `context_generator` (calls the LLM). We mock both so this example
    # runs offline and deterministically.
    fake_construct_paths_return = (
        {},  # resolved_config
        {
            "prompt_file": prompt_file.read_text(encoding="utf-8"),
            "code_file": code_file.read_text(encoding="utf-8"),
        },
        {"output": str(output_file)},  # output_file_paths
        "python",  # language
    )

    fake_example_code = (
        "from math_utils import add\n"
        "\n"
        "if __name__ == \"__main__\":\n"
        "    print(add(2, 3))\n"
    )

    ctx = build_ctx(local=True, quiet=False)

    print("=== Demo 1: default output path, format=None (uses construct_paths default) ===")
    with patch("pdd.context_generator_main.construct_paths", return_value=fake_construct_paths_return), \
         patch("pdd.context_generator_main.context_generator",
               return_value=(fake_example_code, 0.001234, "mock-model-v1")):
        generated_code, total_cost, model_name = context_generator_main(
            ctx=ctx,
            prompt_file=str(prompt_file),
            code_file=str(code_file),
            output=None,           # use construct_paths default
            format=None,
        )

    print(f"model_name = {model_name}")
    print(f"total_cost = ${total_cost:.6f}")
    print(f"wrote: {output_file}")
    print("--- generated code ---")
    print(generated_code)

    print()
    print("=== Demo 2: explicit --output with .yml suffix is honored verbatim ===")
    # Per spec / issue #1183: explicit suffixes MUST be honored verbatim.
    # Even though language is 'yaml' (canonically .yaml), the user's .yml wins.
    yaml_prompt = work_dir / "cfg.prompt"
    yaml_code = work_dir / "cfg.yaml"
    yaml_output = work_dir / "cfg_example.yml"
    yaml_prompt.write_text("Task: produce a sample yaml config.", encoding="utf-8")
    yaml_code.write_text("foo: bar\n", encoding="utf-8")

    yaml_construct_paths_return = (
        {},
        {"prompt_file": "Task: produce a sample yaml config.", "code_file": "foo: bar\n"},
        {"output": str(work_dir / "cfg_default.yaml")},
        "yaml",
    )

    with patch("pdd.context_generator_main.construct_paths", return_value=yaml_construct_paths_return), \
         patch("pdd.context_generator_main.context_generator",
               return_value=("foo: bar\nbaz: qux\n", 0.0001, "mock-model-v1")):
        _, _, _ = context_generator_main(
            ctx=ctx,
            prompt_file=str(yaml_prompt),
            code_file=str(yaml_code),
            output=str(yaml_output),  # user explicitly chose .yml
            format="code",
        )

    print(f"explicit user path honored: {yaml_output} exists? {yaml_output.exists()}")
    rewritten = work_dir / "cfg_example.yaml"
    print(f"would-be rewritten .yaml NOT created: {rewritten} exists? {rewritten.exists()}")


if __name__ == "__main__":
    main()
