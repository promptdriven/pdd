import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(os.environ["PDD_PATH"]).resolve().parent))

from pdd.coverage_contracts import build_coverage_directory  # noqa: E402


root = Path("output") / "coverage_contracts_example"
prompts_dir = root / "prompts"
stories_dir = root / "user_stories"
tests_dir = root / "tests"
for directory in (prompts_dir / "sub", stories_dir, tests_dir):
    directory.mkdir(parents=True, exist_ok=True)

prompt_path = prompts_dir / "sub" / "another.prompt"
prompt_path.write_text(
    """
<contract_rules>
R10: The service MUST validate requests.
R11: The service MUST record accepted requests.
</contract_rules>
""".strip()
    + "\n",
    encoding="utf-8",
)

(stories_dir / "story__accepted_request.md").write_text(
    """
# Accepted request

## Covers
- prompts/sub/another.prompt#R11: Record an accepted request.

## Acceptance Criteria
- The accepted request is recorded.
""".strip()
    + "\n",
    encoding="utf-8",
)

(tests_dir / "test_request_validation.py").write_text(
    '''
def test_request_validation():
    """prompts/sub/another.prompt#R10: validate a request."""
    assert True
'''.strip()
    + "\n",
    encoding="utf-8",
)

results = build_coverage_directory(
    prompts_dir,
    stories_dir=stories_dir,
    tests_dir=tests_dir,
    project_root=root,
)
result = next(item for item in results if item.path == prompt_path)
rules = {rule.rule_id: rule for rule in result.rules}

assert rules["R10"].status == "test-only"
assert rules["R10"].tests == ["test_request_validation"]
assert rules["R11"].status == "story-only"
assert rules["R11"].stories == ["story__accepted_request.md"]

print(f"R10: {rules['R10'].status} via {rules['R10'].tests}")
print(f"R11: {rules['R11'].status} via {rules['R11'].stories}")
