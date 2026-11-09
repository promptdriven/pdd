#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
factory_tmp=$(mktemp -d "${TMPDIR:-/tmp}/pdd-factory.XXXXXXXX")
trap 'rm -rf -- "$factory_tmp"' EXIT
export HOME="$factory_tmp/home"
export XDG_CONFIG_HOME="$factory_tmp/config"
export PDD_STATE_DIR="$factory_tmp/state"
export PDD_INTERPRETER_QUEUE="$factory_tmp/interpreter-queue"
export PDD_SUITE_QUEUE="$factory_tmp/suite-queue"
mkdir -p "$HOME" "$XDG_CONFIG_HOME" "$PDD_STATE_DIR"
unset NODE_OPTIONS PDD_AUTOPILOT_CONTEXT PDD_AGENT_SESSION CODEX_HOME CLAUDE_CONFIG_DIR
# timeout owns only the test process it starts. It cannot select another job.
timeout --signal=TERM --kill-after=5s 890s node --test --test-concurrency=1 test/autopilot-factory.e2e.test.mjs
