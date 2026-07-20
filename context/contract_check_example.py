import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(os.environ["PDD_PATH"]).resolve().parent))

from pdd.contract_check import check_prompt, check_stories  # noqa: E402


root = Path("output") / "contract_check_example"
prompts_dir = root / "prompts"
stories_dir = root / "user_stories"
prompts_dir.mkdir(parents=True, exist_ok=True)
stories_dir.mkdir(parents=True, exist_ok=True)

prompt_path = prompts_dir / "payments.prompt"
prompt_path.write_text(
    """
<contract_rules>
R1: The service MUST accept a payment.
R1a: The service MUST retain the payment reference.
</contract_rules>

<coverage>
R1: story__payment.md
R1a: story__payment_reference.md
</coverage>
""".strip()
    + "\n",
    encoding="utf-8",
)

(stories_dir / "story__payment_reference.md").write_text(
    """
<!-- pdd-story-prompts: payments.prompt -->
# Retain a payment reference

## Covers
- payments.prompt#R1a: Preserve the exact suffixed rule identity.
""".strip()
    + "\n",
    encoding="utf-8",
)

prompt_result = check_prompt(prompt_path)
story_results = check_stories(stories_dir, prompts_dir)
story_issues = [issue for result in story_results for issue in result.issues]

assert not prompt_result.issues
assert not any(issue.code == "UNKNOWN_STORY_REF" for issue in story_issues)

print(f"Prompt issues: {len(prompt_result.issues)}")
print(f"Story issues: {len(story_issues)}")
print("R1a remains distinct from R1 in the story reference.")
