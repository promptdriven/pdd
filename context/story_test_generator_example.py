import os
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(os.environ["PDD_PATH"]).resolve().parent))

from pdd.story_test_generator import (  # noqa: E402
    generate_story_test,
    parse_story_test_spec,
    render_story_test,
)


root = Path("output") / "story_test_generator_example"
story_dir = root / "user_stories"
contract_dir = story_dir / "contracts"
generated_dir = root / "tests" / "story_regression"
contract_dir.mkdir(parents=True, exist_ok=True)
generated_dir.mkdir(parents=True, exist_ok=True)

story_path = story_dir / "story__normalize_name.md"
story_path.write_text(
    """
# Normalize a name

As a user, I want names normalized consistently.
""".strip()
    + "\n",
    encoding="utf-8",
)

(contract_dir / "normalize_name.contract.md").write_text(
    """
## Entry Point
- module: example_names
- callable: normalize_name
- args: ["  Ada Lovelace  "]

## Covers
- R1a: Preserve the suffixed rule identity.

## Oracle
- assert result == "Ada Lovelace"
""".strip()
    + "\n",
    encoding="utf-8",
)

spec = parse_story_test_spec(story_path)
source = render_story_test(spec)
output_path = generated_dir / "test_story_normalize_name.py"
result = generate_story_test(story_path, output=output_path)

assert spec.rule_ids == ("R1A",)
assert "test_story_normalize_name_R1A" in source
assert result.output_path == output_path
assert output_path.read_text(encoding="utf-8") == source

print(f"Generated {result.test_count} test at {result.output_path}")
print(f"Preserved rule IDs: {spec.rule_ids}")

# Remove only this example's dedicated sandbox.
shutil.rmtree(root)
