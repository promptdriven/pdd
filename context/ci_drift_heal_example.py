"""Run ``ci_drift_heal`` safely against a disposable, provider-free project."""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
from contextlib import contextmanager
from pathlib import Path
from typing import Any, Iterator

# Prevent lazy PDD imports from creating ``pdd/__pycache__`` in the checkout.
sys.dont_write_bytecode = True

# Allow this checked-in example to run directly without installing the checkout.
SOURCE_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SOURCE_ROOT))

TIMEOUT_SECONDS = 30
_CHILD_FLAG = "--example-dry-run-child"
_BASENAME = "example_contract"


def main(**kwargs: Any) -> int:
    """Import the PDD entry point only after entering the disposable project."""
    from pdd.ci_drift_heal import main as ci_drift_heal_main  # pylint: disable=import-outside-toplevel

    return ci_drift_heal_main(**kwargs)


@contextmanager
def _working_directory(path: Path) -> Iterator[None]:
    """Temporarily change directory and always restore the caller's CWD."""
    previous = Path.cwd()
    os.chdir(path)
    try:
        yield
    finally:
        os.chdir(previous)


def create_disposable_project(root: Path) -> None:
    """Create one fingerprinted module entirely inside ``root``."""
    prompt = root / "prompts" / f"{_BASENAME}_python.prompt"
    code = root / "pdd" / f"{_BASENAME}.py"
    example = root / "context" / f"{_BASENAME}_example.py"
    test = root / "tests" / f"test_{_BASENAME}.py"

    for directory in (prompt.parent, code.parent, example.parent, test.parent):
        directory.mkdir(parents=True, exist_ok=True)

    (root / ".pddrc").write_text(
        """version: "1.0"
contexts:
  example:
    paths: ["prompts/**"]
    defaults:
      prompts_dir: "prompts"
      generate_output_path: "pdd/"
      example_output_path: "context/"
      test_output_path: "tests/"
      default_language: "python"
""",
        encoding="utf-8",
    )
    prompt.write_text("% Return a stable greeting.\n", encoding="utf-8")
    code.write_text("def greeting() -> str:\n    return 'hello'\n", encoding="utf-8")
    example.write_text(
        "from pdd.example_contract import greeting\n\nprint(greeting())\n",
        encoding="utf-8",
    )
    test.write_text(
        "from pdd.example_contract import greeting\n\n\n"
        "def test_greeting() -> None:\n    assert greeting() == 'hello'\n",
        encoding="utf-8",
    )

    paths = {
        "prompt": prompt,
        "code": code,
        "example": example,
        "test": test,
        "test_files": [test],
    }
    with _working_directory(root):
        from pdd.operation_log import save_fingerprint  # pylint: disable=import-outside-toplevel

        save_fingerprint(_BASENAME, "python", "verify", paths=paths)


def invoke_main(workspace: Path) -> int:
    """Call the real dry-run entry point and return its status unchanged."""
    with _working_directory(workspace):
        return main(
            modules=[_BASENAME],
            budget_cap=0.0,
            skip_ci=False,
            diff_base=None,
            dry_run=True,
            as_json=True,
        )


def _provider_free_environment(workspace: Path) -> dict[str, str]:
    """Build a minimal child environment with isolated config roots."""
    runtime = workspace / ".example-runtime"
    directories = {
        "HOME": runtime / "home",
        "XDG_CONFIG_HOME": runtime / "xdg-config",
        "XDG_CACHE_HOME": runtime / "xdg-cache",
        "XDG_DATA_HOME": runtime / "xdg-data",
        "TMPDIR": runtime / "tmp",
        "AZURE_CONFIG_DIR": runtime / "azure",
        "CLOUDSDK_CONFIG": runtime / "gcloud",
    }
    for directory in directories.values():
        directory.mkdir(parents=True, exist_ok=True)

    # Only process/runtime mechanics cross the boundary. Provider, PDD, Git,
    # cloud, credential, proxy, and ambient Python configuration do not.
    allowed = (
        "PATH",
        "LANG",
        "LC_ALL",
        "SYSTEMROOT",
        "WINDIR",
        "COMSPEC",
        "PATHEXT",
    )
    env = {name: os.environ[name] for name in allowed if name in os.environ}
    env.setdefault("PATH", os.defpath)
    env.update({name: str(path) for name, path in directories.items()})
    env.update(
        {
            "AWS_CONFIG_FILE": str(runtime / "aws" / "config"),
            "AWS_SHARED_CREDENTIALS_FILE": str(
                runtime / "aws" / "credentials"
            ),
            "PYTHONDONTWRITEBYTECODE": "1",
            "PYTHONPATH": str(SOURCE_ROOT),
        }
    )
    return env


def run_dry_run(workspace: Path) -> int:
    """Execute the dry-run in a bounded child and propagate its exact status."""
    try:
        result = subprocess.run(
            [sys.executable, str(Path(__file__).resolve()), _CHILD_FLAG, str(workspace)],
            cwd=workspace,
            env=_provider_free_environment(workspace),
            check=False,
            timeout=TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired:
        print(
            f"ci_drift_heal dry-run timed out after {TIMEOUT_SECONDS} seconds",
            file=sys.stderr,
        )
        return 124
    return result.returncode


def run() -> int:
    """Run the example without changing the source checkout or caller's repo."""
    with tempfile.TemporaryDirectory(prefix="pdd-ci-drift-heal-example-") as temp:
        workspace = Path(temp)
        create_disposable_project(workspace)
        exit_code = run_dry_run(workspace)

    if exit_code != 0:
        print(
            f"ci_drift_heal dry-run failed with exit code {exit_code}",
            file=sys.stderr,
        )
        return exit_code

    print("ci_drift_heal example completed successfully")
    return 0


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == _CHILD_FLAG:
        raise SystemExit(invoke_main(Path(sys.argv[2]).resolve()))
    raise SystemExit(run())
