#!/usr/bin/env bash
# Non-TTY scenario runner for demo/interactive-checkup-1423.
# All checks here are CI-safe (no TTY required).
# Scenarios B2 and C2 require a real terminal — see README.md.

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PASS=0
FAIL=0

pass() { echo "[PASS] $1"; PASS=$((PASS+1)); }
fail() { echo "[FAIL] $1"; FAIL=$((FAIL+1)); }

check_exit() {
  local label="$1" expected="$2" actual="$3"
  if [[ "$actual" -eq "$expected" ]]; then
    pass "$label (exit $actual)"
  else
    fail "$label — expected exit $expected, got $actual"
  fi
}

check_output() {
  local label="$1" pattern="$2" output="$3"
  if echo "$output" | grep -q "$pattern"; then
    pass "$label"
  else
    fail "$label — pattern not found: $pattern"
    echo "  Output was: $output"
  fi
}

run_cmd() {
  # run_cmd CMD... — captures combined stdout+stderr into $CMD_OUT, exit code into $CMD_EXIT
  CMD_OUT=$(python -m pdd "$@" 2>&1) && CMD_EXIT=0 || CMD_EXIT=$?
}

cd "$REPO_ROOT"
echo "=== Interactive Checkup Demo Scenarios (non-TTY) ==="
echo "Working directory: $REPO_ROOT"
echo

# ---------------------------------------------------------------------------
# Scenario A — prompt_lint  (flag validation + clean explain)
# ---------------------------------------------------------------------------
echo "--- Scenario A: prompt_lint_python ---"

# A1: --apply requires --interactive
run_cmd checkup demo/prompts/prompt_lint_python.prompt --apply
check_exit "A1 exit code" 2 "$CMD_EXIT"
check_output "A1 error: requires --interactive" "requires --interactive" "$CMD_OUT"

# A2: --interactive without TTY fires TTY guard
CMD_OUT=$(python -m pdd checkup demo/prompts/prompt_lint_python.prompt --interactive < /dev/null 2>&1) && CMD_EXIT=0 || CMD_EXIT=$?
check_exit "A2 exit code" 2 "$CMD_EXIT"
check_output "A2 error: requires a TTY" "requires a TTY" "$CMD_OUT"

# A3: --explain on a clean prompt exits 0, no findings
run_cmd checkup demo/prompts/prompt_lint_python.prompt --explain
check_exit "A3 exit code" 0 "$CMD_EXIT"
check_output "A3 no findings" "No findings" "$CMD_OUT"

echo

# ---------------------------------------------------------------------------
# Scenario B — fix_main  (non-TTY interactive guard)
# ---------------------------------------------------------------------------
echo "--- Scenario B: fix_main_python ---"

# B1: --interactive without TTY on a different prompt
CMD_OUT=$(python -m pdd checkup demo/prompts/fix_main_python.prompt --interactive < /dev/null 2>&1) && CMD_EXIT=0 || CMD_EXIT=$?
check_exit "B1 exit code" 2 "$CMD_EXIT"
check_output "B1 error: requires a TTY" "requires a TTY" "$CMD_OUT"

echo

# ---------------------------------------------------------------------------
# Scenario C — agentic_change  (requires_clarification field in JSON output)
# ---------------------------------------------------------------------------
echo "--- Scenario C: agentic_change_python ---"

# C1: --explain --json includes requires_clarification in every finding
CMD_OUT=$(python -m pdd checkup demo/prompts/agentic_change_python.prompt --explain --json 2>/dev/null) && CMD_EXIT=0 || CMD_EXIT=$?
check_output "C1 requires_clarification field present" "requires_clarification" "$CMD_OUT"
check_output "C1 findings array present" '"findings"' "$CMD_OUT"
check_output "C1 snapshot finding detected" "snapshot_policy" "$CMD_OUT"

echo

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
echo "=== Results: $PASS passed, $FAIL failed ==="
if [[ "$FAIL" -gt 0 ]]; then
  exit 1
fi
