"""End-to-end exercise of the PR #1501 change-story workflow against a REAL model.

Run from the repo root in a keyed environment, e.g.:

    OPENAI_API_KEY=...  PYTHONPATH=. python scripts/e2e_story_workflow_demo.py
    # or ANTHROPIC_API_KEY / GEMINI_API_KEY / a configured PDD_MODEL_DEFAULT

Nothing is stubbed: it authors a real story + contract from a local issue,
validates it with the real detect oracle, runs the contract-aware fix path, and
drives the off/warn/strict policy gate in the orchestrator hook.
"""
import os
import sys
import tempfile
from pathlib import Path
from types import SimpleNamespace

from pdd.user_story_tests import (
    generate_user_story,
    run_user_story_tests,
    run_user_story_fix,
    _contract_path_for_story,
    _compose_story_oracle,
)
from pdd.agentic_change_orchestrator import _generate_user_story_artifacts_for_change

# Model-tier selector. In this demo env, strength<=0.2 makes llm_invoke try the
# (unauthenticated) PDD cloud + interactive Copilot tier first and stall; 0.5
# selects the keyed Gemini model directly. Strength is a quality/tier knob only.
STRENGTH = float(os.environ.get("PDD_DEMO_STRENGTH", "0.5"))

ISSUE = """# Issue: Upload a CSV and view a summary report

## Summary
Users upload a CSV file and the tool returns a summary report of the contents.

## Acceptance Criteria
- Given a valid CSV, when uploaded, then a summary report (row count + columns) is shown.
- Given a malformed CSV, when uploaded, then a clear validation error is returned.
"""

PROMPT = """% Module: upload
Implement upload(csv_path: str) -> dict that reads a CSV file and returns a
summary report: {"rows": int, "columns": list[str]}. Raise ValueError on a
malformed CSV.
"""


def main():
    wt = Path(tempfile.mkdtemp(prefix="pdd_e2e_"))
    prompts = wt / "prompts"; prompts.mkdir()
    stories = wt / "user_stories"; stories.mkdir()
    prompt_file = prompts / "upload_python.prompt"
    prompt_file.write_text(PROMPT, encoding="utf-8")
    issue_file = wt / "issue_1454.md"
    issue_file.write_text(ISSUE, encoding="utf-8")
    print(f"workspace: {wt}")

    # 1) Generate the human story + machine-checkable contract from the ISSUE.
    print("\n[1] generate_user_story (real LLM) ...")
    ok, msg, cost, model, story_path, linked = generate_user_story(
        prompt_files=[str(prompt_file)],
        issue=str(issue_file),
        stories_dir=str(stories),
        prompts_dir=str(prompts),
        strength=STRENGTH,
    )
    print(f"    success={ok} model={model} cost=${cost:.4f}")
    print(f"    story={story_path}")
    print(f"    linked={linked}")
    if not ok:
        print("    ABORT:", msg); return 1
    contract = _contract_path_for_story(Path(story_path))
    print(f"    contract exists={contract.exists()} -> {contract}")
    print("\n--- combined oracle (story + contract) fed to detect/fix ---")
    print(_compose_story_oracle(Path(story_path), Path(story_path).read_text()))

    # 2) Validate the linked subset with the real detect oracle.
    print("\n[2] run_user_story_tests (real LLM) ...")
    passed, results, vcost, vmodel = run_user_story_tests(
        prompts_dir=str(prompts),
        story_files=[Path(story_path)],
        prompt_files=[prompt_file],
        strength=STRENGTH,
    )
    print(f"    passed={passed} cost=${vcost:.4f} results={results}")

    # 3) Contract-aware repair path.
    print("\n[3] run_user_story_fix (real LLM, contract-aware) ...")
    ctx = SimpleNamespace(obj={})
    fok, fmsg, fcost, fmodel, changed = run_user_story_fix(
        ctx=ctx, story_file=str(story_path), prompts_dir=str(prompts), strength=STRENGTH,
    )
    print(f"    success={fok} cost=${fcost:.4f} changed={changed}\n    msg={fmsg}")

    # 4) Orchestrator hook across the three policies (real generate+validate).
    for policy in ("off", "warn", "strict"):
        os.environ["PDD_STORY_POLICY"] = policy
        # fresh workspace per policy so generation isn't short-circuited by reuse
        files, summary, c, m, block = _generate_user_story_artifacts_for_change(
            issue_url=str(issue_file),
            changed_files=["prompts/upload_python.prompt"],
            worktree_path=wt,
            strength=STRENGTH, temperature=0.0, time_budget=0.25,
            verbose=False, quiet=True,
        )
        print(f"\n[4/{policy}] block={block!r}")
        for line in summary.splitlines():
            print("    " + line)
    return 0


if __name__ == "__main__":
    sys.exit(main())
