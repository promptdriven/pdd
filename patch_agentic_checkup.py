import re

with open('pdd/prompts/agentic_checkup_python.prompt', 'r', encoding='utf-8') as f:
    content = f.read()

req1_old = """1. Function: `run_agentic_checkup(issue_url: str, *, verbose: bool = False, quiet: bool = False, no_fix: bool = False, timeout_adder: float = 0.0, use_github_state: bool = True, reasoning_time: Optional[float] = None, pr_url: Optional[str] = None, review_loop: bool = False, review_only: bool = False, reviewers: str = "codex,claude", reviewer: Optional[str] = None, fixer: Optional[str] = None, max_review_rounds: int = 5, max_review_cost: float = 10.0, max_review_minutes: float = 90.0, require_all_reviewers_clean: bool = True, continue_on_reviewer_limit: bool = False, require_final_fresh_review: bool = True, blocking_severities: Optional[str] = None, clean_reviewer_states: Optional[str] = None) -> Tuple[bool, str, float, str]`"""
req1_new = """1. Function: `run_agentic_checkup(issue_url: str, *, verbose: bool = False, quiet: bool = False, no_fix: bool = False, timeout_adder: float = 0.0, use_github_state: bool = True, reasoning_time: Optional[float] = None, pr_url: Optional[str] = None, review_loop: bool = False, review_only: bool = False, reviewers: str = "codex,claude", reviewer: Optional[str] = None, fixer: Optional[str] = None, max_review_rounds: int = 5, max_review_cost: float = 10.0, max_review_minutes: float = 90.0, require_all_reviewers_clean: bool = True, continue_on_reviewer_limit: bool = False, require_final_fresh_review: bool = True, blocking_severities: Optional[str] = None, clean_reviewer_states: Optional[str] = None, reviewer_fallback: bool = True) -> Tuple[bool, str, float, str]`"""
content = content.replace(req1_old, req1_new)

req11_old = """11. When `review_loop=True`, require PR mode and dispatch to `run_checkup_review_loop()` with a `ReviewLoopContext` and `ReviewLoopConfig`. Map `review_only`, `reviewers`, explicit `reviewer`, explicit `fixer`, `blocking_severities`, and `clean_reviewer_states` onto the config; pass `None` through to take documented defaults."""
req11_new = """11. When `review_loop=True`, require PR mode and dispatch to `run_checkup_review_loop()` with a `ReviewLoopContext` and `ReviewLoopConfig`. Map `review_only`, `reviewers`, explicit `reviewer`, explicit `fixer`, `blocking_severities`, `clean_reviewer_states`, and `reviewer_fallback` onto the config; pass `None` through to take documented defaults."""
content = content.replace(req11_old, req11_new)

with open('pdd/prompts/agentic_checkup_python.prompt', 'w', encoding='utf-8') as f:
    f.write(content)
