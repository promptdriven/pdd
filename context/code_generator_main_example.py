"""Runnable example for ``pdd.code_generator_main``.

Demonstrates the public surface of the orchestration module:

* ``code_generator_main`` — primary entry point that turns a ``.prompt`` file
  into generated source code (returns ``(generated_code, was_incremental,
  total_cost, model_name)``).
* ``ArchitectureConformanceError`` — typed ``click.UsageError`` subclass raised
  when the generated code's exported symbols don't match the interface
  declared in ``architecture.json``. Carries structured fields
  (``prompt_name``, ``output_path``, ``architecture_entry``,
  ``expected_symbols``, ``found_symbols``, ``missing_symbols``,
  ``repair_directive``) so callers like ``pdd sync`` can build a
  repair directive and retry generation.
* ``_verify_architecture_conformance`` — internal helper that performs the
  architecture conformance check and raises ``ArchitectureConformanceError``
  on mismatch.

External dependencies (LLM calls, cloud services, git) are mocked so the
example runs offline in any environment.
"""

import json
import os
import pathlib
import shutil
import sys
from unittest.mock import patch

# Ensure the local pdd package is importable regardless of cwd.
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

import click  # noqa: E402  (after sys.path setup)

from pdd.code_generator_main import (  # noqa: E402
    ArchitectureConformanceError,
    _verify_architecture_conformance,
    code_generator_main,
)


# --- Mock generators ---------------------------------------------------------
# Use **kwargs so the mocks tolerate any keyword forwarding the orchestrator
# applies (strength, temperature, time, verbose, output_schema, language, ...).
def mock_local_code_generator(*args, **kwargs):
    """Stand-in for ``pdd.code_generator.code_generator``.

    Returns ``(generated_code, total_cost, model_name)`` where:
      * generated_code: str — synthetic Python module text
      * total_cost: float (USD) — fake cost so the example doesn't show $0
      * model_name: str — identifier of the (fake) model used
    """
    language = kwargs.get("language", "python")
    return (
        f"# Mock-generated {language} code\n"
        "def hello():\n"
        "    return 'Hello, World!'\n",
        0.0012,
        "mock-local-model-v1",
    )


def mock_incremental_code_generator(*args, **kwargs):
    """Stand-in for ``pdd.incremental_code_generator.incremental_code_generator``.

    Returns ``(updated_code, is_incremental, total_cost, model_name)``.
    """
    existing = kwargs.get("existing_code", "")
    return (
        existing + "\n# patched by mock incremental generator\n",
        True,
        0.0021,
        "mock-incremental-model-v1",
    )


class MockContext:
    """Light click.Context stand-in: only ``ctx.obj`` is consulted."""

    def __init__(self, params):
        self.obj = params or {}


def print_section(title):
    print()
    print("=" * 72)
    print(title)
    print("=" * 72)


def example_full_generation_local(workdir):
    """Demonstrate full local generation when no output file exists yet."""
    print_section("Example 1 — Full generation (local execution)")
    prompt_path = workdir / "hello_python.prompt"
    prompt_path.write_text("Write a Python function that returns 'Hello, World!'.\n")
    output_path = workdir / "hello.py"

    ctx = MockContext({
        "local": True,
        "strength": 0.5,
        "temperature": 0.0,
        "time": 0.25,
        "verbose": False,
        "force": False,
        "quiet": True,
    })

    code, was_incremental, cost, model = code_generator_main(
        ctx=ctx,
        prompt_file=str(prompt_path),
        output=str(output_path),
        original_prompt_file_path=None,
        force_incremental_flag=False,
    )

    print("Generated code (first 80 chars):")
    print(repr(code[:80]))
    print(f"was_incremental: {was_incremental}")
    print(f"total_cost (USD): {cost:.6f}")
    print(f"model_name: {model}")


def example_architecture_conformance_pass(workdir):
    """Conformance check passes when all declared symbols are exported."""
    print_section("Example 2 — Architecture conformance check (passes)")
    arch = [
        {
            "filename": "models_Python.prompt",
            "filepath": "src/models.py",
            "interface": {
                "type": "module",
                "module": {
                    "functions": [
                        {"name": "User", "signature": "class User"},
                        {"name": "make_user", "signature": "def make_user(...)"},
                    ]
                },
            },
        }
    ]
    arch_path = workdir / "architecture.json"
    arch_path.write_text(json.dumps(arch))

    code = (
        "class User:\n"
        "    pass\n"
        "\n"
        "def make_user():\n"
        "    return User()\n"
    )
    # No exception => check passed.
    _verify_architecture_conformance(
        generated_code=code,
        prompt_name="models_Python.prompt",
        arch_path=str(arch_path),
        language="python",
        verbose=False,
    )
    print("Architecture conformance check passed (no exception raised).")


def example_architecture_conformance_failure(workdir):
    """Conformance failure raises ArchitectureConformanceError with structured fields."""
    print_section("Example 3 — Architecture conformance check (fails, structured)")
    arch = [
        {
            "filename": "models_Python.prompt",
            "filepath": "src/models.py",
            "interface": {
                "type": "module",
                "module": {
                    "functions": [
                        {"name": "User", "signature": "class User"},
                        {"name": "Admin", "signature": "class Admin"},
                    ]
                },
            },
        }
    ]
    arch_path = workdir / "architecture.json"
    arch_path.write_text(json.dumps(arch))

    code = "class User:\n    pass\n"  # 'Admin' missing

    try:
        _verify_architecture_conformance(
            generated_code=code,
            prompt_name="models_Python.prompt",
            arch_path=str(arch_path),
            language="python",
            verbose=False,
        )
    except ArchitectureConformanceError as exc:
        # Confirm subclass relationship — existing call sites that catch
        # click.UsageError continue to work unchanged.
        assert isinstance(exc, click.UsageError)
        print(f"prompt_name:        {exc.prompt_name}")
        print(f"output_path:        {exc.output_path!r}")
        print(f"expected_symbols:   {exc.expected_symbols}")
        print(f"found_symbols:      {exc.found_symbols}")
        print(f"missing_symbols:    {exc.missing_symbols}")
        print("repair_directive:")
        for line in exc.repair_directive.splitlines():
            print(f"  {line}")
        # The string message must start with the legacy prefix so existing
        # log-grep tools keep working.
        assert str(exc).startswith("Architecture conformance error for models_Python.prompt:")


def example_camelcase_violation(workdir):
    """camelCase Python exports raise ArchitectureConformanceError too."""
    print_section("Example 4 — camelCase Python exports rejected")
    arch = [
        {
            "filename": "utils_Python.prompt",
            "filepath": "src/utils.py",
            "interface": {
                "type": "module",
                "module": {
                    "functions": [
                        {"name": "processData", "signature": "def processData(...)"},
                    ]
                },
            },
        }
    ]
    arch_path = workdir / "architecture.json"
    arch_path.write_text(json.dumps(arch))

    code = "def processData(data):\n    return data\n"

    try:
        _verify_architecture_conformance(
            generated_code=code,
            prompt_name="utils_Python.prompt",
            arch_path=str(arch_path),
            language="python",
            verbose=False,
        )
    except ArchitectureConformanceError as exc:
        # Per spec: missing_symbols carries the offending camelCase exports.
        print(f"missing_symbols (offending camelCase): {exc.missing_symbols}")
        assert "processData" in exc.missing_symbols
        assert "camelCase" in str(exc)


def main():
    workdir = pathlib.Path("./output/code_generator_main_example_output").resolve()
    if workdir.exists():
        shutil.rmtree(workdir)
    workdir.mkdir(parents=True, exist_ok=True)

    # Patch the orchestrator's external generator dependencies so this script
    # never makes network calls. Patches go where the names are imported.
    with patch(
        "pdd.code_generator_main.local_code_generator_func",
        side_effect=mock_local_code_generator,
    ), patch(
        "pdd.code_generator_main.incremental_code_generator_func",
        side_effect=mock_incremental_code_generator,
    ):
        example_full_generation_local(workdir)
        example_architecture_conformance_pass(workdir)
        example_architecture_conformance_failure(workdir)
        example_camelcase_violation(workdir)

    print()
    print("All examples ran to completion.")


if __name__ == "__main__":
    main()
