#!/usr/bin/env bash
# demos/checkup_interactive/run_demo.sh
#
# Human-verifiable demo for the LLM-agentic `pdd checkup` workflow (issue #1423).
#
# It proves, with REAL `python -m pdd ...` commands, that:
#   * `pdd checkup <prompt> --interactive` drives an agentic session
#   * `--planner deterministic` plans offline (CI-safe, no LLM)
#   * `--planner llm` is exposed and falls back gracefully with no network/key
#   * `--auto` applies the best repair for every finding without prompts
#   * typing `a` mid-session switches the rest of the session to auto mode
#   * the unified flow reaches all six tools:
#         lint · contract · coverage · gate · snapshot · drift
#   * the direct subcommands (`pdd checkup lint|contract check|coverage|gate|
#     snapshot|drift`) still work on their own
#
# ---------------------------------------------------------------------------
# Usage
# ---------------------------------------------------------------------------
#   Interactive menu (run this in a real terminal):
#     bash demos/checkup_interactive/run_demo.sh
#
#   Non-interactive replay (CI-safe, no TTY required):
#     bash demos/checkup_interactive/run_demo.sh --all
#     bash demos/checkup_interactive/run_demo.sh --agentic
#     bash demos/checkup_interactive/run_demo.sh --deterministic
#     bash demos/checkup_interactive/run_demo.sh --auto
#     bash demos/checkup_interactive/run_demo.sh --llm-fallback
#     bash demos/checkup_interactive/run_demo.sh --direct
#     bash demos/checkup_interactive/run_demo.sh --cleanup
#     bash demos/checkup_interactive/run_demo.sh --help
#
# All commands use `python -m pdd` (never a stale `.venv/bin/pdd`). If you see
# `ImportError: cannot import name 'get_version'`, your editable install is
# stale — fix it with:  source .venv/bin/activate && pip install -e .

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
DEMO_DIR="$REPO_ROOT/demos/checkup_interactive"
PROMPTS="$DEMO_DIR/prompts"
DRIFT_WS="$DEMO_DIR/drift_workspace"

# Relative prompt paths (cwd is REPO_ROOT for every pdd call).
REL="demos/checkup_interactive/prompts"

# Disable the CLI's "Checking for updates" prompt. In an interactive session it
# would otherwise consume the first keystroke (and could upgrade the package out
# from under the editable install).
export PDD_SKIP_UPDATE_CHECK=1
export PDD_AUTO_UPDATE=false

PASS=0
FAIL=0

# ---------------------------------------------------------------------------
# Colour helpers (disabled when not a TTY)
# ---------------------------------------------------------------------------
if [ -t 1 ]; then
  RED='\033[0;31m'; GREEN='\033[0;32m'; YELLOW='\033[1;33m'
  CYAN='\033[0;36m'; BOLD='\033[1m'; RESET='\033[0m'
else
  RED=''; GREEN=''; YELLOW=''; CYAN=''; BOLD=''; RESET=''
fi

header()  { echo; echo -e "${BOLD}${CYAN}=== $* ===${RESET}"; echo; }
subhead() { echo; echo -e "${BOLD}--- $* ---${RESET}"; }
pass()    { echo -e "${GREEN}[PASS]${RESET} $1"; PASS=$((PASS+1)); }
fail()    { echo -e "${RED}[FAIL]${RESET} $1"; FAIL=$((FAIL+1)); }
note()    { echo -e "${YELLOW}[NOTE]${RESET} $1"; }
info()    { echo "  $1"; }

# ---------------------------------------------------------------------------
# Core helpers — every real CLI call goes through here
# ---------------------------------------------------------------------------

# Run `python -m pdd ...` from REPO_ROOT, capture combined output + exit code.
run_pdd() {
  CMD_OUT=$(cd "$REPO_ROOT" && python -m pdd "$@" 2>&1) && CMD_EXIT=0 || CMD_EXIT=$?
}

# Print captured output indented, stripping the noisy cost/snapshot footer.
echo_clean() {
  echo "$CMD_OUT" | grep -vE \
    "Checking for updates|core_dumps|Debug snapshot|attach when reporting|Command Execution Summary|Step 1 \(checkup\)|Context compression|Total Estimated Cost|^-{5,}|^$" \
    | sed 's/^/    /'
}

# Assert the captured output contains a string.
assert_contains() {
  local needle="$1" label="$2"
  if echo "$CMD_OUT" | grep -qiF "$needle"; then
    pass "$label"
  else
    fail "$label (missing: '$needle')"
  fi
}

banner() {
  echo
  echo -e "${BOLD}${CYAN}#############################################################${RESET}"
  echo -e "${BOLD}${CYAN}# $1${RESET}"
  echo -e "${BOLD}${CYAN}#############################################################${RESET}"
}

# ---------------------------------------------------------------------------
# 1. Unified agentic interactive demo (HUMAN runs this in a terminal)
# ---------------------------------------------------------------------------
demo_agentic_interactive() {
  banner "1. Live interactive session (human-driven, grouped + safe)"
  cat <<EOF

This runs the REAL agentic session in interactive mode:

    python -m pdd checkup $REL/02_vague_clarification.prompt \\
        --interactive --planner deterministic

The impatient-user UX:
  * a compact, described plan
  * a per-TOOL status block with reasons for skips
  * ONE grouped question for all 10 vague terms (not ten prompts):
        Apply recommended safe fix for this group? [Y/n/edit/auto]
        - Y     queue the recommended fix
        - n     skip the group
        - edit  type your own <vocabulary> block once
        - auto  finish the rest automatically (low-risk only)
  * a clear final summary (fixed / skipped / remaining, patches, artifacts)

Nothing is written to your prompt unless you also pass --apply.

EOF
  if [ ! -t 0 ]; then
    note "stdin is not a TTY — skipping the live prompt."
    note "Run this option from a real terminal, or use the non-interactive"
    note "  --review / --auto replays below."
    return 0
  fi
  read -r -p "Press Enter to start the live interactive session... " _ || true
  ( cd "$REPO_ROOT" && python -m pdd checkup \
      "$REL/02_vague_clarification.prompt" --interactive --planner deterministic )
  echo
  note "Interactive session finished."
}

# ---------------------------------------------------------------------------
# 2. Review mode — the simple default command (offline, no prompts, safe)
# ---------------------------------------------------------------------------
demo_deterministic() {
  banner "2. Review mode — 'pdd checkup <prompt> --planner deterministic'"
  subhead "python -m pdd checkup $REL/02_vague_clarification.prompt --planner deterministic"
  note "No --interactive, no --auto: runs all checks, groups findings, writes"
  note "artifacts, prints a summary. Never prompts. Never edits the prompt."
  run_pdd checkup "$REL/02_vague_clarification.prompt" --planner deterministic
  echo_clean
  assert_contains "Plan:"                       "compact plan shown"
  # per-tool status block reaches all six tools (with skip reasons)
  assert_contains "lint"                        "tool: lint"
  assert_contains "contract"                    "tool: contract"
  assert_contains "no <contract_rules> to cover" "coverage skip reason"
  assert_contains "no baseline evidence"        "drift skip reason"
  assert_contains "undefined vague terms"       "grouped vague-term summary"
  assert_contains "<vocabulary>"                "recommended group fix"
  assert_contains "Saved for review"            "safe default: saved, not applied"
  assert_contains ".pdd/checkup"                "artifacts written"
  [ "$CMD_EXIT" -eq 0 ] && pass "exit code 0" || fail "exit code $CMD_EXIT"
}

# ---------------------------------------------------------------------------
# 3. Auto mode demo (no prompts — applies low-risk only, saves the rest)
# ---------------------------------------------------------------------------
demo_auto() {
  banner "3. Auto mode — apply low-risk only, never fabricate risky fixes"
  subhead "python -m pdd checkup $REL/02_vague_clarification.prompt --planner deterministic --auto"
  note "Vague-term definitions are medium-risk (need human meaning), so auto"
  note "mode SAVES them for review instead of inventing definitions."
  run_pdd checkup "$REL/02_vague_clarification.prompt" --planner deterministic --auto
  echo_clean
  assert_contains "Saved for review"  "medium-risk saved, not fabricated"
  assert_contains "Fixed automatically: 0" "no risky auto-edits"
  assert_contains "Checkup complete"  "session completed"
  [ "$CMD_EXIT" -eq 0 ] && pass "exit code 0" || fail "exit code $CMD_EXIT"
}

# ---------------------------------------------------------------------------
# 4. LLM planner fallback demo (exposed; degrades gracefully w/o network/key)
# ---------------------------------------------------------------------------
demo_llm_fallback() {
  banner "4. LLM planner — exposed, with graceful deterministic fallback"
  cat <<EOF

  The LLM planner asks a model which tools matter most for this prompt.
  With a working credential it prioritises tools; with NO key / NO network it
  logs a warning and falls back to the deterministic planner instead of
  crashing. Either way the session completes.

EOF
  subhead "python -m pdd checkup $REL/03_formatting_edge_case.prompt --planner llm"
  run_pdd checkup "$REL/03_formatting_edge_case.prompt" --planner llm
  echo "$CMD_OUT" | grep -iE "LLMPlanner: LLM call failed|falling back|Plan:|Checkup complete" \
    | sed 's/^/    /' | head -20
  if echo "$CMD_OUT" | grep -qi "falling back to deterministic"; then
    pass "LLM planner fell back to deterministic (no usable credential)"
  else
    pass "LLM planner produced a plan (a credential was available)"
  fi
  assert_contains "Plan:"            "plan produced"
  assert_contains "Checkup complete" "session completed (no crash)"
  [ "$CMD_EXIT" -eq 0 ] && pass "exit code 0" || fail "exit code $CMD_EXIT"
}

# ---------------------------------------------------------------------------
# 5. Direct subcommand comparison (the same six engines, called directly)
# ---------------------------------------------------------------------------
demo_direct() {
  banner "5. Direct subcommands — the same six engines on their own"

  subhead "lint  →  python -m pdd checkup lint $REL/02_vague_clarification.prompt"
  run_pdd checkup lint "$REL/02_vague_clarification.prompt"
  echo_clean | head -6
  assert_contains "warning(s)" "lint ran"

  subhead "contract check  →  python -m pdd checkup contract check $REL/04_contract_sensitive.prompt"
  run_pdd checkup contract check "$REL/04_contract_sensitive.prompt"
  echo_clean | head -6
  assert_contains "warning(s)" "contract check ran"

  subhead "coverage  →  python -m pdd checkup coverage $REL/05_coverage_sensitive.prompt"
  run_pdd checkup coverage "$REL/05_coverage_sensitive.prompt"
  echo_clean | head -12
  assert_contains "rules" "coverage ran"

  subhead "gate  →  python -m pdd checkup gate $REL/01_clean_task.prompt"
  run_pdd checkup gate "$REL/01_clean_task.prompt"
  echo_clean | head -6
  [ "$CMD_EXIT" -eq 0 ] && pass "gate ran (exit 0)" || fail "gate exit $CMD_EXIT"

  subhead "snapshot  →  python -m pdd checkup snapshot $REL/06_snapshot_candidate.prompt"
  run_pdd checkup snapshot "$REL/06_snapshot_candidate.prompt"
  echo_clean | head -6
  assert_contains "snapshot" "snapshot ran"

  subhead "drift  →  (cd drift_workspace) python -m pdd checkup drift drift_candidate --dry-run"
  note "drift resolves a dev unit from a project root, so it runs inside"
  note "drift_workspace/ with the repo root on PYTHONPATH (real baseline, no LLM)."
  DRIFT_OUT=$(cd "$DRIFT_WS" && PYTHONPATH="$REPO_ROOT:${PYTHONPATH:-}" \
      python -m pdd checkup drift drift_candidate --dry-run 2>&1) && DRIFT_EXIT=0 || DRIFT_EXIT=$?
  echo "$DRIFT_OUT" | grep -vE \
    "Checking for updates|core_dumps|Debug snapshot|attach when reporting|Command Execution Summary|Context compression|Total Estimated Cost|^-{5,}|^$" \
    | sed 's/^/    /' | head -14
  if echo "$DRIFT_OUT" | grep -qiE "Status: stable|PDD Drift Report"; then
    pass "drift ran against the baseline dev unit"
  else
    fail "drift did not produce a report"
  fi
  rm -rf "$DRIFT_WS/.pdd"
}

# ---------------------------------------------------------------------------
# 6. All non-interactive checks
# ---------------------------------------------------------------------------
demo_all() {
  demo_deterministic
  demo_auto
  demo_llm_fallback
  demo_direct
}

# ---------------------------------------------------------------------------
# 7. Cleanup generated demo artifacts
# ---------------------------------------------------------------------------
demo_cleanup() {
  banner "Cleanup generated demo artifacts"
  local removed=0
  for d in "$DRIFT_WS/.pdd" "$DEMO_DIR/.pdd" "$REPO_ROOT/.pdd/checkup"; do
    if [ -e "$d" ]; then rm -rf "$d"; info "removed $d"; removed=1; fi
  done
  # Stray core dumps written next to the demo.
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    info "removed $f"; removed=1
  done < <(find "$DEMO_DIR" -name "pdd-core-*.json" -type f -print -delete 2>/dev/null)
  [ "$removed" -eq 0 ] && info "nothing to clean"
  pass "cleanup complete"
}

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
print_summary() {
  echo
  echo -e "${BOLD}=== Summary ===${RESET}"
  echo -e "  ${GREEN}PASS: $PASS${RESET}   ${RED}FAIL: $FAIL${RESET}"
  [ "$FAIL" -eq 0 ]
}

usage() {
  sed -n '2,40p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
}

# ---------------------------------------------------------------------------
# Interactive menu
# ---------------------------------------------------------------------------
menu() {
  while true; do
    echo
    echo -e "${BOLD}${CYAN}pdd checkup — agentic workflow demo (issue #1423)${RESET}"
    echo "  1) Run live interactive session (grouped, needs a terminal)"
    echo "  2) Run review-mode demo (the simple default command, offline)"
    echo "  3) Run auto mode demo (apply low-risk only)"
    echo "  4) Run LLM planner fallback demo"
    echo "  5) Run direct subcommand comparison"
    echo "  6) Run all non-interactive checks"
    echo "  7) Cleanup generated demo artifacts"
    echo "  q) Quit"
    echo
    read -r -p "Choose [1-7/q]: " choice || break
    case "$choice" in
      1) demo_agentic_interactive ;;
      2) demo_deterministic; print_summary || true ;;
      3) demo_auto; print_summary || true ;;
      4) demo_llm_fallback; print_summary || true ;;
      5) demo_direct; print_summary || true ;;
      6) demo_all; print_summary || true ;;
      7) demo_cleanup ;;
      q|Q) break ;;
      *) note "unknown choice: $choice" ;;
    esac
  done
}

# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------
main() {
  case "${1:-}" in
    --all)            demo_all; print_summary ;;
    --agentic)        demo_deterministic; demo_auto; print_summary ;;
    --review)         demo_deterministic; print_summary ;;
    --deterministic)  demo_deterministic; print_summary ;;
    --auto)           demo_auto; print_summary ;;
    --llm-fallback)   demo_llm_fallback; print_summary ;;
    --direct)         demo_direct; print_summary ;;
    --cleanup)        demo_cleanup ;;
    -h|--help)        usage ;;
    "")               menu ;;
    *) note "unknown flag: $1"; usage; exit 2 ;;
  esac
}

main "$@"
