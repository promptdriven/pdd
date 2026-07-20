import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(os.environ["PDD_PATH"]).resolve().parent))

from pdd.contract_ir import parse_prompt_contracts  # noqa: E402


output_dir = Path("output") / "contract_ir_example"
output_dir.mkdir(parents=True, exist_ok=True)
prompt_path = output_dir / "payments.prompt"
prompt_path.write_text(
    """
<contract_rules>
R1: The service MUST accept a payment.
R1a: The service MUST preserve the payment reference suffix exactly.
RULE2a: The service MUST NOT log card data.
</contract_rules>

<coverage>
R1: story__payment.md
R1a: story__payment_reference.md
</coverage>

## Covers
- R1a: The suffixed rule is covered independently of R1.
""".strip()
    + "\n",
    encoding="utf-8",
)

contract = parse_prompt_contracts(prompt_path)
suffixed_rule = contract.rule_by_id("R1A")

assert contract.parse_error is None
assert contract.known_rule_ids == {"R1", "R1A", "RULE2A"}
assert suffixed_rule is not None
assert suffixed_rule.raw_id == "R1A"
assert suffixed_rule.line.startswith("R1a:")

print(f"Parsed rules: {sorted(contract.known_rule_ids)}")
print(f"Exact suffixed rule: {suffixed_rule.raw_id} -> {suffixed_rule.line}")
