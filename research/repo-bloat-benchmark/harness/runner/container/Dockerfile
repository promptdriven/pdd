# Pilot runner (design §8.1.1 hard tier): Python harness + the pinned Codex
# CLI, attached ONLY to the internal (no-egress) network at run time.
FROM node:22-bookworm-slim

# Pinned CLI (CODEX_PIN.md / PREREGISTRATION.md). Bump ONLY with a deliberate
# re-pin: re-run harness.runner.codex_probe against the new build first.
RUN npm install -g @openai/codex@0.142.4

RUN apt-get update \
    && apt-get install -y --no-install-recommends python3 python3-pytest git \
    && rm -rf /var/lib/apt/lists/*

# The benchmark tree is bind-mounted at /bench (docker-compose.yml).
WORKDIR /bench
CMD ["python3", "harness/runner/container/egress_check.py"]
