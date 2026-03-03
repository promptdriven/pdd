"""Example showing how to use one_session_sync for single-session PDD sync."""

import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.one_session_sync import (
    build_one_session_prompt,
    run_one_session_sync,
    _compute_import_base,
    _format_step_display,
    _read_new_progress,
)


def main():
    """Demonstrate the one-session sync workflow with mocked dependencies."""

    # --- Import Base Computation ---
    # Derives the Python dotted import path from a code file path
    root = Path("/proj")
    code = Path("/proj/pdd/crm_models.py")
    import_base = _compute_import_base(code, root)
    print(f"Import base: {import_base}")  # pdd.crm_models

    # --- Step Display Formatting ---
    # Converts progress marker names to user-friendly strings
    print(f"Display: {_format_step_display('example_generate')}")  # Example file created
    print(f"Display: {_format_step_display('crash_fix')}")  # Example runs without errors
    print(f"Display: {_format_step_display('crash_fix_attempt:2')}")  # Crash fix attempt 2
    print(f"Display: {_format_step_display('test_pass')}")  # All tests passing

    # --- Build Prompt ---
    # Assembles the mega-prompt from module spec, code, and template
    tmp = Path("/tmp/one_session_example")
    tmp.mkdir(parents=True, exist_ok=True)

    prompt_file = tmp / "spec.prompt"
    prompt_file.write_text("% Goal\nBuild a calculator module.\n")
    code_file = tmp / "calculator.py"
    code_file.write_text("def add(a, b): return a + b\n")

    pdd_files = {
        "prompt": prompt_file,
        "code": code_file,
        "example": tmp / "calculator_example.py",
        "test": tmp / "test_calculator.py",
    }

    template_text = (
        "# {basename} ({language})\n"
        "Prompt: {prompt_path}\nCode: {code_path}\n"
        "Example: {example_path}\nTest: {test_path}\n"
        "Root: {project_root}\nCoverage: {target_coverage}%\n"
        "Progress: {progress_file}\nImport: {import_base}\n"
        "Verify step: {verify_step_num}\nTest step: {test_step_num}\n"
        "---\n{resolved_prompt_content}\n---\n{code_content}\n"
    )

    with patch("pdd.one_session_sync.load_prompt_template", return_value=template_text), \
         patch("pdd.one_session_sync.preprocess", side_effect=lambda c, **kw: c):
        prompt = build_one_session_prompt(
            basename="calculator",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp,
            target_coverage=85.0,
        )
    print(f"\n--- Built Prompt (first 200 chars) ---")
    print(prompt[:200])

    # --- Run One-Session Sync (mocked) ---
    print(f"\n--- Running one-session sync ---")
    with patch("pdd.one_session_sync.run_agentic_task") as mock_task, \
         patch("pdd.one_session_sync.load_prompt_template", return_value=template_text), \
         patch("pdd.one_session_sync.preprocess", side_effect=lambda c, **kw: c):
        mock_task.return_value = (True, "All steps complete", 0.42, "anthropic")

        result = run_one_session_sync(
            basename="calculator",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp,
            target_coverage=85.0,
            quiet=True,
        )

    print(f"Success           : {result['success']}")
    print(f"Total cost        : ${result['total_cost']:.2f}")
    print(f"Model             : {result['model_name']}")
    print(f"Operations done   : {result['operations_completed']}")
    print(f"Errors            : {result['errors']}")

    # --- Progress File Reading ---
    # Simulates reading step progress markers from the progress file
    progress = tmp / ".pdd_one_session_progress_calculator"
    progress.write_text(
        "STEP_COMPLETE:example_generate\n"
        "STEP_COMPLETE:crash_fix\n"
        "STEP_COMPLETE:verify\n"
        "STEP_COMPLETE:test_generate\n"
        "STEP_COMPLETE:test_pass\n"
        "STEP_COMPLETE:done\n"
    )
    new_steps = _read_new_progress(progress, skip_count=2)
    print(f"\nNew steps (after skipping 2): {new_steps}")
    # ['verify', 'test_generate', 'test_pass', 'done']

    # Cleanup
    import shutil
    shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    main()
