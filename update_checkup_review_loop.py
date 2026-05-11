import json
with open('pdd/prompts/checkup_review_loop_python.prompt', 'r') as f:
    content = f.read()

reason = "PR-mode primary-reviewer/fixer review loop for pdd checkup to ensure issues and PRs are reviewed."
interface = {
  "type": "module",
  "module": {
    "functions": [
      {"name": "parse_reviewers", "signature": "(value: str | Sequence[str] | None) -> Tuple[str, ...]", "returns": "Tuple[str, ...]"},
      {"name": "run_checkup_review_loop", "signature": "(*, context: ReviewLoopContext, config: ReviewLoopConfig, cwd: Path, verbose: bool = False, quiet: bool = False, use_github_state: bool = True) -> Tuple[bool, str, float, str]", "returns": "Tuple[bool, str, float, str]"}
    ]
  }
}

tags = f"""<pdd-reason>{reason}</pdd-reason>
<pdd-interface>
{json.dumps(interface, indent=2)}
</pdd-interface>
"""

with open('pdd/prompts/checkup_review_loop_python.prompt', 'w') as f:
    f.write(tags + content)
