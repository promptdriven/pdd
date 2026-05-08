"""Example demonstrating ``pdd.fix_main.fix_main``.

This script shows how to invoke :func:`fix_main` for both single-pass and
iterative loop fixes. Heavy dependencies (LLM calls, cloud auth, pytest
subprocess) are mocked so the example is fully standalone — it requires no
network access, no API keys, and no installed compiler toolchains.

Inputs (positional / keyword):
    ctx (click.Context): Click context whose ``ctx.obj`` carries shared CLI
        options (``strength`` 0.0–1.0, ``temperature`` 0.0–1.0, ``time``
        0.0–1.0 thinking budget, ``verbose``, ``quiet``, ``force``, ``local``,
        ``context`` directory override, ``confirm_callback``).
    prompt_file (str): Path to the prompt that produced the buggy code.
    code_file (str): Path to the buggy code to fix.
    unit_test_file (str): Path to the failing unit-test file.
    error_file (str): Path to a pre-captured pytest error log (required for
        single-pass mode; created/overwritten in loop mode).
    output_test / output_code / output_results (Optional[str]): Destinations
        for the fixed test, fixed code, and analysis log respectively.
    loop (bool): If True, iterate via ``fix_error_loop``; otherwise single-pass.
    verification_program (Optional[str]): Required when ``loop=True`` — a small
        Python script that exits 0 when the fixed code imports/runs.
    max_attempts (int): Maximum loop iterations.
    budget (float): Maximum dollar cost for the fix.
    auto_submit (bool): If True, post a successful fix to the cloud.

Returns:
    Tuple[bool, str, str, int, float, str]: (success, fixed_unit_test,
    fixed_code, attempts, total_cost_usd, model_name).
"""

from __future__ import annotations

import os
import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

# Ensure the local pdd package is importable regardless of where this example
# is executed from (e.g. ``python context/fix_main_example.py``).
_PROJECT_ROOT = Path(__file__).resolve().parent.parent
if str(_PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(_PROJECT_ROOT))

import click
from rich.console import Console

from pdd.fix_main import fix_main


console = Console()


def _make_ctx() -> click.Context:
    """Build a ``click.Context`` with the keys ``fix_main`` reads from ``obj``."""

    @click.command()
    def _dummy() -> None:
        pass

    ctx = click.Context(_dummy)
    ctx.obj = {
        "verbose": False,
        "strength": 0.5,
        "temperature": 0.0,
        "time": 0.25,
        "force": True,
        "quiet": False,
        "local": True,  # Force local execution → skip cloud auth path.
        "context": None,
        "confirm_callback": None,
    }
    return ctx


def _seed_files(workdir: Path) -> dict[str, str]:
    """Create the small set of input/output files ``fix_main`` expects."""
    workdir.mkdir(parents=True, exist_ok=True)

    code_file = workdir / "calculator.py"
    code_file.write_text("def add(a, b):\n    return a - b  # buggy\n")

    test_file = workdir / "test_calculator.py"
    test_file.write_text(
        "from calculator import add\n\n"
        "def test_add():\n"
        "    assert add(2, 3) == 5\n"
    )

    prompt_file = workdir / "calculator_python.prompt"
    prompt_file.write_text("Write `add(a, b)` returning the sum of two numbers.")

    verify_file = workdir / "verify_calc.py"
    verify_file.write_text(
        "from calculator import add\n"
        "assert add(1, 2) == 3\n"
    )

    error_file = workdir / "errors.log"
    error_file.write_text("AssertionError: assert -1 == 5")

    return {
        "code": str(code_file),
        "test": str(test_file),
        "prompt": str(prompt_file),
        "verify": str(verify_file),
        "error": str(error_file),
        "output_test": str(workdir / "test_calculator_fixed.py"),
        "output_code": str(workdir / "calculator_fixed.py"),
        "output_results": str(workdir / "fix_results.log"),
    }


def _run_with_mocks(paths: dict[str, str], *, loop: bool) -> tuple:
    """Invoke ``fix_main`` with all heavy dependencies mocked."""

    construct_paths_return = (
        {},  # resolved_config
        {
            "prompt_file": "PROMPT BODY",
            "code_file": "def add(a, b):\n    return a - b\n",
            "unit_test_file": "from calculator import add\n",
            **({} if loop else {"error_file": "AssertionError: -1 != 5"}),
        },
        {
            "output_test": paths["output_test"],
            "output_code": paths["output_code"],
            "output_results": paths["output_results"],
        },
        None,
    )

    fixed_test = "from calculator import add\n\ndef test_add():\n    assert add(2, 3) == 5\n"
    fixed_code = "def add(a, b):\n    return a + b\n"

    fix_errors_return = (
        True,                     # update_unit_test
        True,                     # update_code
        fixed_test,               # fixed unit test
        fixed_code,               # fixed code
        "Switched - to + so add() now sums.",  # analysis_results
        0.0123,                   # total_cost (USD)
        "mock-model",             # model name
    )

    fix_loop_return = (
        True,                     # success
        fixed_test,
        fixed_code,
        2,                        # attempts
        0.0456,                   # total_cost
        "mock-model-loop",
    )

    with patch("pdd.fix_main.construct_paths", return_value=construct_paths_return), \
         patch("pdd.fix_main.fix_errors_from_unit_tests", return_value=fix_errors_return), \
         patch("pdd.fix_main.fix_error_loop", return_value=fix_loop_return), \
         patch("pdd.fix_main.run_pytest_on_file", return_value=(0, 0, 0, "passed")), \
         patch("pdd.fix_main.CloudConfig.is_running_in_cloud", return_value=False):
        return fix_main(
            ctx=_make_ctx(),
            prompt_file=paths["prompt"],
            code_file=paths["code"],
            unit_test_file=paths["test"],
            error_file=paths["error"],
            output_test=paths["output_test"],
            output_code=paths["output_code"],
            output_results=paths["output_results"],
            loop=loop,
            verification_program=paths["verify"] if loop else None,
            max_attempts=3,
            budget=1.0,
            auto_submit=False,            # avoid cloud submission path entirely
            agentic_fallback=False,
            strength=None,                # falls back to ctx.obj["strength"]
            temperature=None,
        )


def main() -> None:
    """Run both modes and print the returned tuple values."""
    workdir = Path(__file__).resolve().parent / "_fix_main_example_output"
    paths = _seed_files(workdir)

    console.print("[bold blue]== fix_main example ==[/bold blue]")
    console.print()

    console.print("[bold green]-- Single-pass mode --[/bold green]")
    success, fixed_test, fixed_code, attempts, cost, model = _run_with_mocks(paths, loop=False)
    console.print(f"success={success}  attempts={attempts}  cost=${cost:.4f}  model={model}")
    console.print()

    console.print("[bold green]-- Loop mode --[/bold green]")
    success, fixed_test, fixed_code, attempts, cost, model = _run_with_mocks(paths, loop=True)
    console.print(f"success={success}  attempts={attempts}  cost=${cost:.4f}  model={model}")
    console.print()

    console.print("[bold blue]Done.[/bold blue]")


if __name__ == "__main__":
    main()
