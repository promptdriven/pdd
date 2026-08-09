"""Worker loop for the isolated ``agent`` container."""

from __future__ import annotations

import argparse
import os
import sys

from harness.runner.agent_launcher import run_worker_loop


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--request-dir",
        default=os.environ.get("RB_AGENT_REQUEST_DIR", "/bench/agent-requests"),
    )
    parser.add_argument("--poll-interval", type=float, default=0.1)
    args = parser.parse_args(argv)
    run_worker_loop(args.request_dir, poll_interval_seconds=args.poll_interval)
    return 0


if __name__ == "__main__":
    sys.exit(main())
