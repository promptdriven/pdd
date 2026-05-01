from __future__ import annotations

import sys
from pathlib import Path
from unittest.mock import MagicMock, patch

project_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(project_root))

from pdd.agentic_common import (
    detect_control_token,
    get_agent_provider_preference,
    get_available_agents,
    run_agentic_task,
    validate_cached_state,
)


def main() -> None:
    """Demonstrate core agentic helpers with mocked provider execution."""
    print(f"Provider preference: {get_agent_provider_preference()}")

    with patch("pdd.agentic_common._find_cli_binary") as find_cli:
        find_cli.side_effect = lambda name: f"/usr/bin/{name}" if name == "claude" else None
        print(f"Available providers with mocked CLI discovery: {get_available_agents()}")

    token_match = detect_control_token(
        "Ran the suite locally.\nAll 12 tests passed successfully.",
        "ALL_TESTS_PASS",
    )
    print(f"Detected test-pass token: {bool(token_match)}")

    rewound = validate_cached_state(
        last_completed_step=3,
        step_outputs={
            "step1": "ok",
            "step2": "FAILED: verifier rejected output",
            "step3": "cached but should be ignored",
        },
        step_order=["step1", "step2", "step3"],
        quiet=True,
    )
    print(f"Validated resume point: {rewound}")

    fake_response = MagicMock(
        returncode=0,
        stdout='{"result":"Agent finished the requested review.","total_cost_usd":0.01}',
        stderr="",
    )
    with patch("pdd.agentic_common.get_available_agents", return_value=["anthropic"]), \
         patch("pdd.agentic_common.get_agent_provider_preference", return_value=["anthropic"]), \
         patch("pdd.agentic_common._find_cli_binary", return_value="/usr/bin/claude"), \
         patch("pdd.agentic_common._subprocess_run", return_value=fake_response):
        success, output, cost, provider = run_agentic_task(
            "Summarize the current checkup state.",
            cwd=project_root,
            quiet=True,
        )

    print(f"Agentic task success: {success}")
    print(f"Provider used: {provider}")
    print(f"Cost: ${cost:.2f}")
    print(f"Output: {output}")


if __name__ == "__main__":
    main()
