import json
with open('pdd/prompts/agentic_checkup_python.prompt', 'r') as f:
    content = f.read()

reason = "Entry point for agentic checkup. Fetches issue/PR context and dispatches to orchestrators."
interface = {
  "type": "module",
  "module": {
    "functions": [
      {"name": "run_agentic_checkup", "signature": "(issue_url: str, *, verbose: bool = False, quiet: bool = False, no_fix: bool = False, timeout_adder: float = 0.0, use_github_state: bool = True, reasoning_time: Optional[float] = None, pr_url: Optional[str] = None, review_loop: bool = False, review_only: bool = False, reviewers: str = \"codex,claude\", reviewer: Optional[str] = None, fixer: Optional[str] = None, max_review_rounds: int = 5, max_review_cost: float = 10.0, max_review_minutes: float = 90.0, require_all_reviewers_clean: bool = True, continue_on_reviewer_limit: bool = False, require_final_fresh_review: bool = True, blocking_severities: Optional[str] = None, clean_reviewer_states: Optional[str] = None, reviewer_fallback: bool = True) -> Tuple[bool, str, float, str]", "returns": "Tuple[bool, str, float, str]"}
    ]
  }
}

tags = f"""<pdd-reason>{reason}</pdd-reason>
<pdd-interface>
{json.dumps(interface, indent=2)}
</pdd-interface>
"""

with open('pdd/prompts/agentic_checkup_python.prompt', 'w') as f:
    f.write(tags + content)
