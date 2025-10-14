# context/agentic_fix_example_minimal.py
import os
import sys
import tempfile
from pathlib import Path
from rich import print as rprint
from rich.panel import Panel

# Import from your package
from pdd.agentic_fix import run_agentic_fix

def main() -> None:
    # Make an isolated temp project
    tmpdir = tempfile.TemporaryDirectory()
    root = Path(tmpdir.name).resolve()

    # Minimal repo layout + files
    (root / "pdd").mkdir(parents=True, exist_ok=True)
    (root / "tests").mkdir(parents=True, exist_ok=True)
    (root / "prompts").mkdir(parents=True, exist_ok=True)

    code_file = root / "pdd" / "demo.py"
    test_file = root / "tests" / "test_demo.py"
    prompt_file = root / "prompts" / "demo_python.prompt"
    error_log_file = root / "agentic_fix_example.log"

    # A tiny buggy function (will fail the test)
    code_file.write_text(
        "def add(a, b):\n"
        "    # BUG: returns subtraction instead of sum\n"
        "    return a - b\n",
        encoding="utf-8",
    )

    # A tiny pytest test
    test_file.write_text(
        "from pdd.demo import add\n"
        "\n"
        "def test_add():\n"
        "    assert add(2, 3) == 5\n",
        encoding="utf-8",
    )

    # A minimal prompt the agent will see
    prompt_file.write_text(
        "Fix add(a,b) so it returns the mathematical sum.\n",
        encoding="utf-8",
    )

    # Ensure the error log exists (empty is fine; run_agentic_fix can preflight)
    error_log_file.write_text("", encoding="utf-8")

    # Change CWD to the temp project so relative imports/tests resolve
    os.chdir(root)

    # Call the agentic fallback
    success, message, est_cost, used_model = run_agentic_fix(
        prompt_file=str(prompt_file),
        code_file=str(code_file),
        unit_test_file=str(test_file),
        error_log_file=str(error_log_file),
    )

    # Report
    rprint(Panel.fit(f"Temp project: {root}"))
    rprint(Panel.fit(f"Success: {success}"))
    rprint(Panel.fit(f"Message: {message}"))
    rprint(Panel.fit(f"Estimated agent cost: ${est_cost:.6f}"))
    rprint(Panel.fit(f"Agent model used: {used_model}"))
    rprint(Panel.fit(f"Error log -> {error_log_file}"))

    # Show final files (even if agent couldn’t run without keys/CLIs)
    try:
        final_code = code_file.read_text(encoding="utf-8")
        final_test = test_file.read_text(encoding="utf-8")
        rprint(Panel.fit(f"Final code:\n{final_code}"))
        rprint(Panel.fit(f"Final test:\n{final_test}"))
    except Exception as e:
        rprint(Panel.fit(f"[yellow]Note:[/yellow] Could not read final files: {e}"))

if __name__ == "__main__":
    main()
