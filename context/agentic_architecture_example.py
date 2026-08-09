"""Example showing how to use run_agentic_architecture for GitHub issue-based architecture generation."""

import json
import sys
from pathlib import Path
from unittest.mock import patch

# Prepend the worktree root so the in-tree `pdd` package wins over any
# already-installed copy that may not yet have the new symbols (e.g. when
# running this example from a clone before `pip install -e .`).
project_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(project_root))

from pdd.agentic_architecture import run_agentic_architecture


def _fake_gh_command(args):
    """Stand-in for `_run_gh_command` so the example runs without `gh` or network.

    Returns canned issue/comment payloads matching what `gh api` would emit.
    """
    cmd = " ".join(args)
    if "/issues/" in cmd and "/comments" not in cmd:
        return True, json.dumps({
            "title": "Build modular reporting service",
            "body": "Add a service that ingests events and emits a daily report.",
            "user": {"login": "example-user"},
            "comments_url": "https://api.github.com/repos/example/repo/issues/42/comments",
            "labels": [],
        })
    if cmd.endswith("/comments") or "/comments?" in cmd or "comments --paginate" in cmd:
        return True, "[]"
    return True, "{}"


def main():
    """Demonstrate the agentic architecture workflow with everything mocked.

    `gh api` (issue + comments fetch) and the orchestrator are stubbed so the
    example runs without a working `gh` install or a real GitHub issue.
    """

    issue_url = "https://github.com/example/repo/issues/42"

    print(f"Running agentic architecture workflow for: {issue_url}")
    print("-" * 60)

    # Stand-in repo path returned by the patched `_ensure_repo_context` so the
    # example never tries to actually `gh repo clone example/repo`.
    fake_repo_path = Path("/tmp/example-pdd-project")
    (fake_repo_path / ".git").mkdir(parents=True, exist_ok=True)

    with patch("pdd.agentic_architecture._check_gh_cli", return_value=True), \
         patch("pdd.agentic_architecture._run_gh_command", side_effect=_fake_gh_command), \
         patch("pdd.agentic_architecture._ensure_repo_context",
               return_value=(fake_repo_path, None)), \
         patch("pdd.agentic_architecture.run_agentic_architecture_orchestrator") as mock_orchestrator:
        mock_orchestrator.return_value = (
            True,
            "Architecture generated. Created architecture.json with 6 modules.",
            2.50,
            "anthropic",
            ["architecture.json", "architecture_diagram.html"],
        )

        # Default discovery: walks up from cwd through PDD markers (.pddrc/.pdd/
        # or sources/ + PRD/spec markdown — innermost wins) before falling back
        # to .git. Path.home() is skipped so ~/.pdd doesn't anchor a project at $HOME.
        success, message, cost, model, output_files = run_agentic_architecture(
            issue_url=issue_url,
            verbose=False,
            quiet=False,
        )

        print("\n--- Default-discovery result ---")
        print(f"Success       : {success}")
        print(f"Cost          : ${cost:.2f}")
        print(f"Model Used    : {model}")
        print(f"Output Files  : {output_files}")
        print(f"Message       : {message}")

        # Explicit override: pin the project root, bypassing marker discovery.
        # CLI equivalent: pdd generate --project-root <path> <issue-url>
        nested_project = fake_repo_path

        success, message, cost, model, output_files = run_agentic_architecture(
            issue_url=issue_url,
            verbose=False,
            quiet=True,
            project_root=str(nested_project),
        )

        print("\n--- Explicit-override result ---")
        print(f"Success       : {success}")
        print(f"Project root  : {nested_project}")
        print(f"Cost          : ${cost:.2f}")
        print(f"Model Used    : {model}")
        print(f"Output Files  : {output_files}")
        print(f"Message       : {message}")


if __name__ == "__main__":
    main()
