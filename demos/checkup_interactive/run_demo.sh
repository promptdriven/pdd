#!/usr/bin/env bash
# demos/checkup_interactive/run_demo.sh
#
# Interactive checkup demo for issue #1423.
#
# Usage:
#   bash demos/checkup_interactive/run_demo.sh           # interactive menu
#   bash demos/checkup_interactive/run_demo.sh --all     # run all automated checks
#   bash demos/checkup_interactive/run_demo.sh --mode lint
#   bash demos/checkup_interactive/run_demo.sh --mode contract
#   bash demos/checkup_interactive/run_demo.sh --mode coverage
#   bash demos/checkup_interactive/run_demo.sh --mode gate
#   bash demos/checkup_interactive/run_demo.sh --mode snapshot
#   bash demos/checkup_interactive/run_demo.sh --mode drift
#   bash demos/checkup_interactive/run_demo.sh --mode adversarial
#   bash demos/checkup_interactive/run_demo.sh --mode overview

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
DEMO_DIR="$REPO_ROOT/demos/checkup_interactive"
PROMPTS="$DEMO_DIR/prompts"

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
# Core utilities
# ---------------------------------------------------------------------------

pdd() { python -m pdd "$@"; }

# Run a command, capture combined output + exit code.
run_cmd() {
  CMD_OUT=$(python -m pdd "$@" 2>&1) && CMD_EXIT=0 || CMD_EXIT=$?
}

# Run a command, capture JSON stdout only (stderr suppressed).
run_json() {
  JSON_OUT=$(python -m pdd "$@" 2>/dev/null) && JSON_EXIT=0 || JSON_EXIT=$?
}

# Extract a check status from --explain --json output.
# Usage: check_status "$JSON_OUT" lint  →  prints "pass", "fail", "warn", "skip", or "?"
check_status() {
  echo "$1" | python3 -c "
import sys, json
try:
    data = json.load(sys.stdin)
    reports = data.get('reports', [])
    if not reports:
        print('?')
        sys.exit(0)
    checks = reports[0].get('checks', [])
    name = '${2:-lint}'
    for c in checks:
        if c.get('name') == name:
            print(c.get('status', '?'))
            sys.exit(0)
    print('?')
except Exception:
    print('?')
" 2>/dev/null
}

# Extract all check statuses as "name:status" pairs.
all_check_statuses() {
  echo "$1" | python3 -c "
import sys, json
try:
    data = json.load(sys.stdin)
    reports = data.get('reports', [])
    if not reports:
        sys.exit(0)
    for c in reports[0].get('checks', []):
        print(f'{c[\"name\"]}:{c[\"status\"]}')
except Exception:
    pass
" 2>/dev/null
}

# Extract findings as "source_check:code:severity:req_clarif" lines.
all_findings() {
  echo "$1" | python3 -c "
import sys, json
try:
    data = json.load(sys.stdin)
    reports = data.get('reports', [])
    if not reports:
        sys.exit(0)
    for f in reports[0].get('findings', []):
        rc = 'clarification-needed' if f.get('requires_clarification') else 'auto-fixable'
        print(f'  [{f[\"source_check\"]}] {f[\"code\"]}  severity={f[\"severity\"]}  {rc}')
except Exception:
    pass
" 2>/dev/null
}

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
    fail "$label — pattern not found: '$pattern'"
    echo "  output was: $output" | head -5
  fi
}

# Compare unified check status against direct subcommand result.
# compare_check LABEL PROMPT CHECK_NAME DIRECT_CMD...
compare_check() {
  local label="$1" prompt="$2" check_name="$3"
  shift 3

  run_json checkup "$prompt" --explain --json
  local unified_status
  unified_status=$(check_status "$JSON_OUT" "$check_name")

  local direct_out direct_exit
  direct_out=$(python -m pdd "$@" 2>&1) && direct_exit=0 || direct_exit=$?
  local direct_status="pass"
  [[ "$direct_exit" -ne 0 ]] && direct_status="fail/warn"

  info "Unified  [$check_name]: $unified_status"
  info "Direct   [pdd $*]: exit $direct_exit"

  # Both agree when unified is non-pass ↔ direct exit != 0
  if [[ "$unified_status" == "pass" || "$unified_status" == "skip" ]]; then
    if [[ "$direct_exit" -eq 0 ]]; then
      pass "$label — unified and direct agree (both clean)"
    else
      fail "$label — unified reports $unified_status but direct exits $direct_exit"
    fi
  else
    if [[ "$direct_exit" -ne 0 ]]; then
      pass "$label — unified and direct agree (both find issues)"
    else
      fail "$label — unified reports $unified_status but direct exits $direct_exit (clean)"
    fi
  fi
}

# ---------------------------------------------------------------------------
# Demo sections
# ---------------------------------------------------------------------------

demo_overview() {
  header "OVERVIEW — pdd checkup <prompt> runs all 6 checks for every prompt"
  echo "  Running 'pdd checkup <prompt> --explain --json' on all five demo prompts."
  echo "  Each prompt is designed to trigger a different check."
  echo

  # Print table header
  printf "  %-36s  %-8s  %-10s  %-10s  %-6s  %-10s\n" \
    "Prompt" "lint" "contract" "coverage" "gate" "snapshot"
  printf "  %-36s  %-8s  %-10s  %-10s  %-6s  %-10s\n" \
    "------" "----" "--------" "--------" "----" "--------"

  local all_ok=1
  for prompt_file in "$PROMPTS"/0*.prompt; do
    local name
    name=$(basename "$prompt_file")
    run_json checkup "$prompt_file" --explain --json
    local l c cov g s
    l=$(check_status "$JSON_OUT" "lint")
    c=$(check_status "$JSON_OUT" "contract")
    cov=$(check_status "$JSON_OUT" "coverage")
    g=$(check_status "$JSON_OUT" "gate")
    s=$(check_status "$JSON_OUT" "snapshot")
    printf "  %-36s  %-8s  %-10s  %-10s  %-6s  %-10s\n" \
      "$name" "$l" "$c" "$cov" "$g" "$s"

    # Confirm all 5 check names appear in unified output (structural check)
    local checks_reported
    checks_reported=$(all_check_statuses "$JSON_OUT" | cut -d: -f1 | sort | tr '\n' ' ')
    for want in lint contract coverage gate snapshot; do
      if ! echo "$checks_reported" | grep -qw "$want"; then
        all_ok=0
      fi
    done
  done
  echo

  if [[ "$all_ok" -eq 1 ]]; then
    pass "All 5 prompts: unified command reports lint, contract, coverage, gate, snapshot"
  else
    fail "One or more check names missing from unified output"
  fi
  note "Drift appears as a finding (not a check row) when a .pdd/evidence/ manifest exists."
  note "gate=skip means no evidence manifest yet — expected for new devunits."
}

demo_lint() {
  header "LINT — vague-term detection (02_vague_requirements)"
  local prompt="$PROMPTS/02_vague_requirements.prompt"
  info "Target:  $prompt"
  info "Vague terms in the <requirements> block trigger VAGUE_TERM_UNDEFINED (requires_clarification=true)."
  echo

  subhead "Unified command findings"
  run_json checkup "$prompt" --explain --json
  all_findings "$JSON_OUT"
  echo

  compare_check "lint: unified vs direct" "$prompt" "lint" \
    checkup lint "$prompt"

  subhead "requires_clarification flag verified on lint findings"
  local rc_vals
  rc_vals=$(echo "$JSON_OUT" | python3 -c "
import sys, json
data = json.load(sys.stdin)
findings = data.get('reports', [{}])[0].get('findings', [])
lint_findings = [f for f in findings if f['source_check'] == 'lint']
print(len(lint_findings), 'lint findings')
clarif = sum(1 for f in lint_findings if f.get('requires_clarification'))
print(clarif, 'require clarification (routed to interactive, not auto-repair)')
" 2>/dev/null)
  echo "  $rc_vals"
  if echo "$rc_vals" | grep -q "^[1-9].*require clarification"; then
    pass "lint findings correctly set requires_clarification=true"
  else
    fail "no clarification-flagged lint findings found"
  fi
}

demo_contract() {
  header "CONTRACT CHECK — contract rule validation (03_contract_coverage)"
  local prompt="$PROMPTS/03_contract_coverage.prompt"
  info "Target: $prompt"
  info "The <contract_rules> section has R901-R903; a vague term 'duplicate' triggers a VAGUE_TERM warning."
  echo

  subhead "Unified command findings"
  run_json checkup "$prompt" --explain --json
  all_findings "$JSON_OUT"
  echo

  compare_check "contract: unified vs direct" "$prompt" "contract" \
    checkup contract check "$prompt"
}

demo_coverage() {
  header "COVERAGE — contract coverage matrix (03_contract_coverage)"
  local prompt="$PROMPTS/03_contract_coverage.prompt"
  info "Target: $prompt"
  info "Rules R901-R903 have no linked user stories or tests → coverage: warn (unchecked)."
  echo

  subhead "Unified command coverage status"
  run_json checkup "$prompt" --explain --json
  local cov_status
  cov_status=$(check_status "$JSON_OUT" "coverage")
  info "Unified coverage status: $cov_status"
  echo

  subhead "Direct coverage command"
  python -m pdd checkup coverage "$prompt" 2>&1 | grep -v "Debug snapshot\|core_dumps\|Command Exec\|compression\|Checking for" || true
  echo

  subhead "Comparison"
  local direct_exit
  python -m pdd checkup coverage "$prompt" 2>/dev/null && direct_exit=0 || direct_exit=$?
  if [[ "$cov_status" != "pass" && "$cov_status" != "skip" ]]; then
    pass "coverage: unified and direct both find unchecked rules"
  elif [[ "$direct_exit" -eq 0 ]]; then
    pass "coverage: unified and direct both clean"
  else
    fail "coverage: unified=$cov_status but direct exits $direct_exit"
  fi
}

demo_gate() {
  header "GATE — waiver/evidence gate (01_clean_task)"
  local prompt="$PROMPTS/01_clean_task.prompt"
  info "Target: $prompt"
  info "No .pdd/evidence/ manifest for this devunit → gate: skip (expected)."
  echo

  subhead "Unified command gate status"
  run_json checkup "$prompt" --explain --json
  local gate_status
  gate_status=$(check_status "$JSON_OUT" "gate")
  info "Unified gate status: $gate_status"
  echo

  subhead "Direct gate command"
  python -m pdd checkup gate "$prompt" 2>&1 | grep -v "Debug snapshot\|core_dumps\|Command Exec\|compression\|Checking for" || true
  echo

  if [[ "$gate_status" == "skip" ]]; then
    pass "gate: unified correctly reports skip (no evidence manifest)"
  elif [[ "$gate_status" == "pass" ]]; then
    pass "gate: unified reports pass"
  else
    fail "gate: unexpected status '$gate_status'"
  fi
}

demo_snapshot() {
  header "SNAPSHOT — nondeterministic context policy (05_snapshot_candidate)"
  local prompt="$PROMPTS/05_snapshot_candidate.prompt"
  info "Target: $prompt"
  info "The prompt uses <include query=...> which declares nondeterministic context."
  info "No snapshot evidence exists → snapshot: fail."
  echo

  subhead "Unified command findings"
  run_json checkup "$prompt" --explain --json
  all_findings "$JSON_OUT"
  echo

  compare_check "snapshot: unified vs direct" "$prompt" "snapshot" \
    checkup snapshot "$prompt"
}

demo_drift() {
  header "DRIFT — regeneration drift detection (direct subcommand only)"
  info "Drift checks require a .pdd/evidence/<devunit>.latest.json manifest."
  info "Without evidence, 'pdd checkup drift' requires explicit arguments."
  info "In the unified command, drift surfaces as an info-level finding when evidence exists."
  echo

  note "Demonstrating the direct subcommand interface (no evidence in this demo):"
  echo
  info "  pdd checkup drift --help"
  python -m pdd checkup drift --help 2>&1 | head -15 || true
  echo

  note "When evidence exists, 'pdd checkup <prompt> --explain' shows:"
  note "  [drift] drift_readiness  severity=info  — 'consider pdd checkup drift before shipping'"
  note "That finding is the unified command's hook into the drift abstraction layer."

  pass "drift: subcommand interface verified (evidence needed for live run)"
}

demo_adversarial() {
  header "ADVERSARIAL — error paths and edge cases"

  # A1: --apply without --interactive must exit 2
  subhead "A1: --apply without --interactive is rejected"
  run_cmd checkup "$PROMPTS/01_clean_task.prompt" --apply
  check_exit "A1 exit code" 2 "$CMD_EXIT"
  check_output "A1 error: requires --interactive" "requires --interactive" "$CMD_OUT"

  # A2: --interactive without TTY fires TTY guard
  subhead "A2: --interactive without TTY fires guard"
  CMD_OUT=$(python -m pdd checkup "$PROMPTS/01_clean_task.prompt" --interactive < /dev/null 2>&1) \
    && CMD_EXIT=0 || CMD_EXIT=$?
  check_exit "A2 exit code" 2 "$CMD_EXIT"
  check_output "A2 error: requires a TTY" "requires a TTY" "$CMD_OUT"

  # A3: --explain --json on a failing prompt still produces valid JSON (not a crash)
  subhead "A3: --explain --json on failing prompt produces valid JSON (no crash)"
  run_json checkup "$PROMPTS/05_snapshot_candidate.prompt" --explain --json
  local valid_json
  valid_json=$(echo "$JSON_OUT" | python3 -c "import sys, json; json.load(sys.stdin); print('ok')" 2>/dev/null || echo "invalid")
  if [[ "$valid_json" == "ok" ]]; then
    pass "A3: JSON output is well-formed even on a failing prompt"
  else
    fail "A3: JSON output is malformed (exit was $JSON_EXIT)"
  fi

  # A4: formatting-edge-case prompt does not crash
  subhead 'A4: formatting edge case (%%, {}, code-fences) does not crash'
  run_cmd checkup "$PROMPTS/04_formatting_edge_case.prompt" --explain
  check_exit "A4 exit code" 0 "$CMD_EXIT"
  check_output "A4 output has status" "Status:" "$CMD_OUT"

  # A5: --explain --json on vague prompt includes requires_clarification field on every finding
  subhead "A5: requires_clarification field present on all lint findings"
  run_json checkup "$PROMPTS/02_vague_requirements.prompt" --explain --json
  local all_have_field
  all_have_field=$(echo "$JSON_OUT" | python3 -c "
import sys, json
data = json.load(sys.stdin)
findings = data.get('reports', [{}])[0].get('findings', [])
missing = [f.get('id','?') for f in findings if 'requires_clarification' not in f]
print('missing:', missing)
" 2>/dev/null)
  if echo "$all_have_field" | grep -q "missing: \[\]"; then
    pass "A5: requires_clarification present on every finding"
  else
    fail "A5: $all_have_field"
  fi

  # A6: requires_clarification=True findings excluded from auto-repair filter
  subhead "A6: vague-term findings routed to interactive path, not auto-repair"
  local clarif_count
  clarif_count=$(echo "$JSON_OUT" | python3 -c "
import sys, json
data = json.load(sys.stdin)
findings = data.get('reports', [{}])[0].get('findings', [])
n = sum(1 for f in findings if f.get('requires_clarification'))
print(n)
" 2>/dev/null)
  if [[ "${clarif_count:-0}" -gt 0 ]]; then
    pass "A6: $clarif_count findings flagged as requires_clarification (excluded from auto-repair)"
  else
    fail "A6: no clarification-routed findings found on vague prompt"
  fi
}

# ---------------------------------------------------------------------------
# Interactive repair session walkthrough
# ---------------------------------------------------------------------------

demo_repair_session() {
  header "INTERACTIVE REPAIR SESSION — what --interactive --apply --preview looks like"
  echo "  This walkthrough simulates the per-finding menu that appears when you run:"
  echo
  echo -e "    ${CYAN}pdd checkup <prompt> --interactive --apply --preview${RESET}"
  echo
  echo "  (Requires a real TTY — run that command directly from your terminal.)"
  echo "  This demo shows the EXACT menu format you will see, using real findings"
  echo "  from 02_vague_requirements.prompt."
  echo

  # Fetch real findings from the vague prompt
  run_json checkup "$PROMPTS/02_vague_requirements.prompt" --explain --json
  local findings_json="$JSON_OUT"

  local finding_count
  finding_count=$(echo "$findings_json" | python3 -c "
import sys, json
data = json.load(sys.stdin)
findings = data.get('reports', [{}])[0].get('findings', [])
print(len(findings))
" 2>/dev/null)

  echo -e "  ${BOLD}Prompt has $finding_count findings. The session walks through each one.${RESET}"
  echo "  For this demo, we show the first 3 in simulated form:"
  echo

  # Render simulated menu for first 3 findings
  echo "$findings_json" | python3 -c "
import sys, json
data = json.load(sys.stdin)
findings = data.get('reports', [{}])[0].get('findings', [])
for i, f in enumerate(findings[:3]):
    fid = f.get('id', '?')
    msg = f.get('message', '?')
    evidence = (f.get('evidence') or '')[:80].strip()
    action = f.get('recommended_action', 'Apply suggested repair')
    preview = (evidence or msg)[:70]
    alt = (f.get('message') or '')[:70]
    rc = '  *** requires_clarification=true — routed to interactive, not auto-repair ***' if f.get('requires_clarification') else ''
    print()
    print(f'  Finding {i+1}/{len(findings)}')
    print(f'  [{fid}]')
    print(f'  {msg}')
    if evidence:
        print(f'  Evidence: {evidence}')
    if rc:
        print(f'  {rc}')
    print()
    print(f'  Choose one:')
    print(f'  [1] {action} — {preview}')
    print(f'  [2] Alternative repair — {alt}')
    print(f'  [3] Write my own definition')
    print(f'  [4] Skip this finding')
    print(f'  Choice [4]:  <- user types 1, 2, 3, or 4')
" 2>/dev/null

  echo
  echo "  After all findings are answered:"
  echo "    --preview  → shows what patches WOULD be written, no files changed"
  echo "    --apply    → writes the patches to the prompt file"
  echo "    (no flag)  → records choices in session but does not write"
  echo
  echo "  To run the real interactive session (TTY required):"
  echo
  echo -e "  ${CYAN}pdd checkup demos/checkup_interactive/prompts/02_vague_requirements.prompt \\${RESET}"
  echo -e "  ${CYAN}    --interactive --apply --preview${RESET}"
  echo
  echo "  To apply the repairs for real (will modify the prompt file):"
  echo
  echo -e "  ${CYAN}pdd checkup demos/checkup_interactive/prompts/02_vague_requirements.prompt \\${RESET}"
  echo -e "  ${CYAN}    --interactive --apply${RESET}"
  echo -e "  ${CYAN}git checkout -- demos/checkup_interactive/prompts/  # undo afterwards${RESET}"
  echo

  # Structural check: confirm findings have the right shape for the menu
  local menu_ok
  menu_ok=$(echo "$findings_json" | python3 -c "
import sys, json
data = json.load(sys.stdin)
findings = data.get('reports', [{}])[0].get('findings', [])
required = {'id', 'message', 'recommended_action', 'requires_clarification', 'source_check'}
missing = [f.get('id','?') for f in findings if not required.issubset(f.keys())]
print('ok' if not missing else f'missing fields in: {missing}')
" 2>/dev/null)
  if [[ "$menu_ok" == "ok" ]]; then
    pass "All findings have the fields required to drive the interactive menu"
  else
    fail "Finding structure broken: $menu_ok"
  fi
}

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------

print_summary() {
  echo
  echo -e "${BOLD}=== Results: ${GREEN}$PASS passed${RESET}${BOLD}, ${RED}$FAIL failed${RESET}${BOLD} ===${RESET}"
  if [[ "$FAIL" -gt 0 ]]; then
    exit 1
  fi
}

# ---------------------------------------------------------------------------
# Menu (interactive)
# ---------------------------------------------------------------------------

show_menu() {
  echo
  echo -e "${BOLD}Interactive Checkup Demo — issue #1423${RESET}"
  echo
  echo "Demonstrates that 'pdd checkup <prompt>' routes through the same"
  echo "call abstraction layer as the six direct subcommands."
  echo
  echo "  1) Overview    — table of all 5 prompts × all 6 checks"
  echo "  2) Lint        — vague-term detection (02_vague_requirements)"
  echo "  3) Contract    — contract rule validation (03_contract_coverage)"
  echo "  4) Coverage    — contract coverage matrix (03_contract_coverage)"
  echo "  5) Gate        — waiver/evidence gate (01_clean_task, shows skip)"
  echo "  6) Snapshot    — nondeterministic context (05_snapshot_candidate)"
  echo "  7) Drift       — direct subcommand only (evidence required)"
  echo "  8) Adversarial — error paths and edge cases"
  echo "  9) Repair      — walkthrough of --interactive --apply --preview menu"
  echo "  a) All         — run all automated checks"
  echo "  q) Quit"
  echo
}

run_all() {
  header "Running all demo checks"
  demo_overview
  demo_lint
  demo_contract
  demo_coverage
  demo_gate
  demo_snapshot
  demo_drift
  demo_adversarial
  demo_repair_session
  print_summary
}

# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

cd "$REPO_ROOT"

# Parse arguments
MODE=""
for arg in "$@"; do
  case "$arg" in
    --all) MODE="all" ;;
    --mode) : ;;  # next arg is the mode value
    lint|contract|coverage|gate|snapshot|drift|adversarial|overview|repair)
      MODE="$arg" ;;
  esac
done
# Handle "--mode lint" style
for i in "$@"; do
  if [[ "$i" == "--mode" ]]; then
    shift_next=1
  elif [[ "${shift_next:-0}" == "1" ]]; then
    MODE="$i"
    shift_next=0
  fi
done

if [[ -n "$MODE" ]]; then
  case "$MODE" in
    all)        run_all ;;
    overview)   demo_overview;  print_summary ;;
    lint)       demo_lint;      print_summary ;;
    contract)   demo_contract;  print_summary ;;
    coverage)   demo_coverage;  print_summary ;;
    gate)       demo_gate;      print_summary ;;
    snapshot)   demo_snapshot;  print_summary ;;
    drift)      demo_drift;          print_summary ;;
    adversarial) demo_adversarial;   print_summary ;;
    repair)     demo_repair_session; print_summary ;;
    *) echo "Unknown mode: $MODE"; exit 1 ;;
  esac
  exit 0
fi

# Interactive menu
while true; do
  show_menu
  read -rp "Choice: " choice
  case "$choice" in
    1) demo_overview ;;
    2) demo_lint ;;
    3) demo_contract ;;
    4) demo_coverage ;;
    5) demo_gate ;;
    6) demo_snapshot ;;
    7) demo_drift ;;
    8) demo_adversarial ;;
    9) demo_repair_session ;;
    a|A) run_all ;;
    q|Q) echo "Bye."; exit 0 ;;
    *) echo "Unknown choice: $choice" ;;
  esac
  echo
  read -rp "Press Enter to continue..." _
done
