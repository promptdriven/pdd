"""Example showing how to use run_checkup_prompt for unified prompt-space source-set health checks."""

import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.checkup_prompt_main import run_checkup_prompt


def main():
    """Demonstrate the run_checkup_prompt orchestrator with mocked sub-engines."""
    target = "refund_payment"
    print(f"Running checkup prompt for: {target}")
    print("-" * 60)

    with patch("pdd.checkup_prompt_main.scan_prompt") as mock_lint, \
         patch("pdd.checkup_prompt_main.build_coverage") as mock_cov, \
         patch("pdd.checkup_prompt_main.run_gate_policy") as mock_gate, \
         patch("pdd.checkup_prompt_main.parse_prompt_contracts") as mock_ir:

        mock_lint.return_value = []
        mock_cov.return_value = {"gaps": []}
        mock_gate.return_value = (True, "gate passed")
        mock_ir.return_value = {
            "contract_rules": [],
            "vocabulary": {},
            "coverage": {},
            "waivers": [],
            "capabilities": [],
        }

        success, message, cost, model = run_checkup_prompt(
            target=target,
            explain=False,
            interactive=False,
            apply=False,
            quiet=False,
            verbose=False,
        )

    print(f"Success: {success}")
    print(f"Message: {message}")
    print(f"Cost: ${cost:.4f}")
    print(f"Model: {model}")

    # With --explain
    print("\n--- with explain=True ---")
    with patch("pdd.checkup_prompt_main.scan_prompt", return_value=[]), \
         patch("pdd.checkup_prompt_main.build_coverage", return_value={"gaps": []}), \
         patch("pdd.checkup_prompt_main.run_gate_policy", return_value=(True, "gate passed")), \
         patch("pdd.checkup_prompt_main.parse_prompt_contracts", return_value={}):

        success, message, cost, model = run_checkup_prompt(
            target=target,
            explain=True,
            interactive=False,
            apply=False,
            quiet=False,
            verbose=True,
        )

    print(f"Success: {success}")
    print(f"Message: {message}")


if __name__ == "__main__":
    main()
