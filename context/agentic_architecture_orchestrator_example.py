"""
Example usage of pdd.agentic_architecture_orchestrator.

Demonstrates how to invoke ``run_agentic_architecture_orchestrator`` end-to-end.
The orchestrator runs a multi-step LLM-driven workflow (PRD analysis, complexity
gate, design, validation, etc.). Real LLM calls are expensive and slow, so this
example mocks the agentic dispatch (``run_agentic_task``) and the workflow-state
helpers, and feeds the orchestrator a happy-path label-driven response per step.

Inputs (kwargs to ``run_agentic_architecture_orchestrator``):
    - issue_url, issue_content, repo_owner, repo_name, issue_number,
      issue_author, issue_title: GitHub issue metadata (strings/int).
    - cwd (Path): project root for generated artifacts.
    - verbose (bool), quiet (bool): logging flags.
    - timeout_adder (float, seconds): added to per-step timeouts.
    - use_github_state (bool): persist workflow state to GitHub comments.

Returns a 5-tuple:
    (success: bool, final_message: str, total_cost: float (USD),
     model_used: str, output_files: List[str])

Run from any directory:
    python context/agentic_architecture_orchestrator_example.py
"""

import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch


# Resolve project root and prefer the local ``pdd`` package over any
# pre-installed copy in site-packages.
_PROJECT_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if _PROJECT_ROOT not in sys.path:
    sys.path.insert(0, _PROJECT_ROOT)
# Drop any pre-imported ``pdd`` modules so the local copy is used.
for _name in [m for m in list(sys.modules) if m == "pdd" or m.startswith("pdd.")]:
    del sys.modules[_name]

from pdd.agentic_architecture_orchestrator import (  # noqa: E402
    run_agentic_architecture_orchestrator,
)


def _make_run_agentic_task_side_effect(cwd: Path):
    """
    Build a side_effect that returns realistic step outputs keyed by ``label``.

    The orchestrator passes ``label="step1"``, ``"step1b"``, ``"step5b"``, etc.
    to ``run_agentic_task`` so each step can be distinguished.
    """

    def side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        cost = 0.05  # USD per simulated step

        # Order matters: more specific labels first.
        if "step1b" in label:
            return (True, "COMPLEXITY_RESULT: MANAGEABLE\nComplexity score: 2/14.", cost, "gpt-4")
        if "step5b" in label:
            return (True, "VALIDATION_RESULT: VALID\nAll requirements covered.", cost, "gpt-4")
        if "step7b" in label:
            return (True, "REVIEW_RESULT: CLEAN\nArchitecture verified.", cost, "gpt-4")
        if "step8_5" in label:
            ctx_dir = cwd / "prompts" / "_context"
            ctx_dir.mkdir(parents=True, exist_ok=True)
            (ctx_dir / "data_dictionary.yaml").write_text("models: {}\n")
            return (
                True,
                "FILES_CREATED: prompts/_context/data_dictionary.yaml",
                cost,
                "gpt-4",
            )
        if "step9b" in label:
            return (True, "AUDIT_RESULT: CONSISTENT", cost, "gpt-4")
        if "step10" in label or "step11" in label or "step12" in label:
            return (True, "VALIDATION_RESULT: VALID", cost, "gpt-4")
        if "step7" in label:
            (cwd / "architecture.json").write_text(
                '[{"priority": 1, "filename": "models_Python.prompt", '
                '"dependencies": [], "description": "Data models"}]'
            )
            return (True, "FILES_CREATED: architecture.json", cost, "gpt-4")
        if "step8" in label:
            (cwd / ".pddrc").write_text("prompts_dir: prompts\n")
            return (True, "FILES_CREATED: .pddrc", cost, "gpt-4")
        if "step9" in label:
            return (True, "FILES_CREATED: prompts/models_Python.prompt", cost, "gpt-4")
        if label == "step5":
            # Step 5 has structural validation: must be >=200 chars and contain
            # module-design markers (module/dependency/priority/interface/## modules).
            return (
                True,
                "## Modules\n"
                "- models: priority 1, dependency none, interface SQLAlchemy ORM models\n"
                "- auth: priority 2, depends on models, interface POST /login\n"
                "- api: priority 3, depends on auth + models, interface REST /api/*\n"
                "- ui: priority 4, depends on api, interface React SPA\n"
                "Module dependency graph and per-module priority assignments above.\n",
                cost,
                "gpt-4",
            )
        # Generic placeholder for steps 2, 2b, 3, 4, 6.
        return (True, f"Output for {label}", cost, "gpt-4")

    return side_effect


def main() -> int:
    """Run a fully-mocked orchestrator pass and print the result."""
    print("Running agentic_architecture_orchestrator example (mocked)...")
    print("-" * 64)

    with tempfile.TemporaryDirectory() as tmp:
        cwd = Path(tmp)

        with patch(
            "pdd.agentic_architecture_orchestrator.run_agentic_task",
            side_effect=_make_run_agentic_task_side_effect(cwd),
        ), patch(
            "pdd.agentic_architecture_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_architecture_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_architecture_orchestrator.clear_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_architecture_orchestrator.load_prompt_template",
            return_value="Mock prompt template body for {issue_title}",
        ), patch(
            "pdd.agentic_architecture_orchestrator.generate_mermaid_code",
            return_value="graph TD; A-->B;",
        ), patch(
            "pdd.agentic_architecture_orchestrator.generate_html",
            return_value="<html><body>diagram</body></html>",
        ), patch(
            "pdd.agentic_architecture_orchestrator.HAS_MERMAID",
            True,
        ):
            success, message, total_cost, model_used, output_files = (
                run_agentic_architecture_orchestrator(
                    issue_url="https://github.com/example/myapp/issues/42",
                    issue_content=(
                        "Build an e-commerce platform: user auth, product catalog, "
                        "shopping cart, and checkout. Next.js frontend + FastAPI + PostgreSQL."
                    ),
                    repo_owner="example",
                    repo_name="myapp",
                    issue_number=42,
                    issue_author="product_owner",
                    issue_title="PRD: E-commerce MVP",
                    cwd=cwd,
                    verbose=False,
                    quiet=True,
                    timeout_adder=0.0,
                    use_github_state=False,
                )
            )

            print(f"Success      : {success}")
            print(f"Message      : {message}")
            print(f"Total cost   : ${total_cost:.2f} USD")
            print(f"Model used   : {model_used}")
            print("Output files :")
            for path in output_files:
                print(f"  - {path}")
            print()
            print("Artifacts in temp cwd:")
            for entry in sorted(p for p in cwd.rglob("*") if p.is_file()):
                print(f"  - {entry.relative_to(cwd)}")

    print("-" * 64)
    print("Example complete.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
