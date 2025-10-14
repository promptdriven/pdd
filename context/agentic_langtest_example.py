# context/agentic_langtest_example.py
import os
import tempfile
import subprocess
from pathlib import Path
from rich import print as rprint
from rich.panel import Panel

from pdd.agentic_langtest import default_verify_cmd_for, missing_tool_hints


def run_local(cmd: str, cwd: Path) -> tuple[int, str]:
    """
    Run a shell command in `cwd`, ensuring the temp project is importable.
    Returns (exit_code, combined_output).
    """
    env = os.environ.copy()
    env["PYTHONPATH"] = str(cwd) + (os.pathsep + env.get("PYTHONPATH", ""))
    proc = subprocess.run(
        cmd,
        shell=True,            # default_verify_cmd_for returns shell-friendly pipelines
        text=True,
        cwd=str(cwd),
        capture_output=True,
        check=False,
        env=env,
    )
    out = (proc.stdout or "") + (("\n" + proc.stderr) if proc.stderr else "")
    return proc.returncode, out


def main() -> None:
    """
    Self-contained example that:
      - creates a temporary Python project with a tiny passing test,
      - builds a verification command via agentic_langtest,
      - runs it locally and prints the result.
    No external files or env are required.
    """
    # Create an isolated temp project
    tmpdir = tempfile.TemporaryDirectory()
    root = Path(tmpdir.name).resolve()

    # Project layout
    pkg_dir = root / "pdd"
    tests_dir = root / "tests"
    pkg_dir.mkdir(parents=True, exist_ok=True)
    tests_dir.mkdir(parents=True, exist_ok=True)

    # Make it a real Python package so `from pdd.demo import mul` works
    (pkg_dir / "__init__.py").write_text("", encoding="utf-8")

    code_file = pkg_dir / "demo.py"
    test_file = tests_dir / "test_demo.py"

    # Minimal code + test (should pass)
    code_file.write_text(
        "def mul(a, b):\n"
        "    return a * b\n",
        encoding="utf-8",
    )
    test_file.write_text(
        "from pdd.demo import mul\n"
        "\n"
        "def test_mul():\n"
        "    assert mul(3, 4) == 12\n",
        encoding="utf-8",
    )

    # We know this demo is Python; avoid repo-specific CSV requirements.
    lang = "python"
    rprint(Panel.fit(f"Detected language (example): {lang}"))

    # Build a conservative verification command for the language
    verify_cmd = default_verify_cmd_for(lang, str(test_file))
    if not verify_cmd:
        rprint(Panel.fit("[red]No default verify command for this language.[/red]"))
        hint = missing_tool_hints(lang, verify_cmd, root)
        if hint:
            rprint(Panel.fit(hint))
        return

    # Substitute placeholders like agentic_fix does
    verify_cmd = verify_cmd.replace("{test}", str(test_file.resolve())).replace("{cwd}", str(root))

    # Helpful install/tooling hints if something seems missing
    hint = missing_tool_hints(lang, verify_cmd, root)
    if hint:
        rprint(Panel.fit(hint))

    # Run in the temp project
    os.chdir(root)
    code, output = run_local(verify_cmd, root)

    rprint(Panel.fit(f"Project: {root}"))
    rprint(Panel.fit(f"Verify command:\n{verify_cmd}"))
    rprint(Panel.fit(f"Exit code: {code}"))
    rprint(Panel.fit(f"Output:\n{output}"))
    if code == 0:
        rprint(Panel.fit("[green]Verification passed[/green]"))
    else:
        rprint(Panel.fit("[red]Verification failed[/red]"))


if __name__ == "__main__":
    main()
