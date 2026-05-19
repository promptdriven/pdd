#!/usr/bin/env bash
# demo.sh — walks through every acceptance criterion of `pdd prompt lint`
#
# Usage (from repo root):
#   cd /path/to/pdd
#   bash examples/prompt_lint_demo/demo.sh
#
# Requires: pdd installed in the active environment (pip install -e .)

set -euo pipefail
export PDD_SKIP_UPDATE_CHECK=1   # prevent auto-upgrade from overwriting the dev install
PDD="pdd --quiet"
DEMO=examples/prompt_lint_demo
VAGUE=$DEMO/prompts/payment_api_vague_python.prompt
CLEAN=$DEMO/prompts/payment_api_clean_python.prompt
STORIES=$DEMO/stories

hr()  { echo; printf '%.0s─' {1..72}; echo; }
hdr() { hr; echo "  $1"; hr; }

# ─────────────────────────────────────────────────────────────────────────────
hdr "① Non-LLM default mode"
echo "Scans for vague terms deterministically — no API key required."
echo
echo "▶  $PDD prompt lint $VAGUE"
$PDD prompt lint "$VAGUE" || true   # exits 1 when warnings found

# ─────────────────────────────────────────────────────────────────────────────
hdr "② Defined terms suppress warnings"
echo "Add a <vocabulary> block and every warning disappears."
echo
echo "▶  $PDD prompt lint $CLEAN"
$PDD prompt lint "$CLEAN"           # exits 0

# ─────────────────────────────────────────────────────────────────────────────
hdr "③ Works on stories  (--stories)"
echo "Scans user-story Acceptance Criteria for undefined vague terms."
echo
echo "▶  $PDD prompt lint --stories $STORIES $CLEAN"
$PDD prompt lint --stories "$STORIES" "$CLEAN" || true
echo
echo "▶  $PDD prompt lint --stories $STORIES"
$PDD prompt lint --stories "$STORIES" || true

# ─────────────────────────────────────────────────────────────────────────────
hdr "④ Suggests additions to <vocabulary>"
echo "Every issue carries a ready-to-paste suggestion."
echo
echo "▶  $PDD prompt lint $VAGUE  (look for 'Suggestion:' lines below)"
$PDD prompt lint "$VAGUE" || true

# ─────────────────────────────────────────────────────────────────────────────
hdr "⑤ Emits JSON  (--json)"
echo "Machine-readable output for CI pipelines, dashboards, or jq."
echo
echo "▶  $PDD prompt lint --json $VAGUE"
$PDD prompt lint --json "$VAGUE" || true
echo
echo "▶  Pretty-print first issue with jq:"
$PDD prompt lint --json "$VAGUE" 2>/dev/null | \
    python3 -c "
import json, sys
data = json.load(sys.stdin)
issue = data[0]['issues'][0]
print(json.dumps(issue, indent=2))
" || true

# ─────────────────────────────────────────────────────────────────────────────
hdr "⑥ Read-only by default — files are never modified"
echo "Without --apply the file content is unchanged."
echo
TMPFILE=$(mktemp /tmp/pdd_demo.XXXXXX)
cp "$VAGUE" "$TMPFILE"
echo "▶  $PDD prompt lint $TMPFILE   (then diff)"
$PDD prompt lint "$TMPFILE" || true
if diff -q "$VAGUE" "$TMPFILE" > /dev/null; then
    echo "  ✓ File unchanged."
else
    echo "  ✗ File was modified! (unexpected)"
fi
rm "$TMPFILE"

# ─────────────────────────────────────────────────────────────────────────────
hdr "⑦ --apply writes vocabulary suggestions"
echo "The deterministic pass generates placeholder suggestions."
echo "--apply only writes concrete (non-placeholder) definitions — typically"
echo "from the LLM pass. To demonstrate, we inject a concrete suggestion"
echo "via Python and then call apply_suggestions directly."
echo
TMPFILE=$(mktemp /tmp/pdd_demo.XXXXXX)
cp "$VAGUE" "$TMPFILE"
# Use the same interpreter as the pdd command
PY=$(command -v python3.12 || command -v python3)
$PY - "$TMPFILE" <<'PYEOF'
import sys
from pathlib import Path
from pdd.prompt_lint import LintIssue, apply_suggestions

path = Path(sys.argv[1])
concrete_issues = [
    LintIssue(
        level="warn", term="authorized merchant",
        section="contract_rules",
        line="1. Only authorized merchants may initiate a charge.",
        message="demo",
        suggestion="authorized merchant: a caller presenting a Bearer JWT with iss='merchant-svc' and a merchant_id in the allowlist table",
    ),
    LintIssue(
        level="warn", term="duplicate transaction",
        section="contract_rules",
        line="2. Reject duplicate transactions gracefully.",
        message="demo",
        suggestion="duplicate transaction: a charge whose idempotency_key matches a pending or succeeded row within the last 24 hours",
    ),
]
n = apply_suggestions(path, concrete_issues)
print(f"  ✓ {n} suggestion(s) written to <vocabulary> block.")
PYEOF
echo
echo "  Diff (original vs. after --apply):"
diff "$VAGUE" "$TMPFILE" | head -30 || true
rm "$TMPFILE"

# ─────────────────────────────────────────────────────────────────────────────
hdr "⑧ Optional LLM ambiguity review  (--ambiguity --llm)"
echo "Requires a configured LLM provider. Skip this step if no API key is set."
echo "Shows 'Possible interpretations' and richer suggestions per term."
echo
echo "▶  $PDD prompt lint --ambiguity --llm $VAGUE"
echo "   (skipping live call in demo — use the command above manually)"

# ─────────────────────────────────────────────────────────────────────────────
hdr "⑨ --strict mode — exit 2 for CI hard-failure"
echo "Escalates all warnings to errors. Useful as a pre-commit / CI gate."
echo
echo "▶  $PDD prompt lint --strict $VAGUE"
$PDD prompt lint --strict "$VAGUE" || echo "  Exit code: $? (expected 2)"

hr
echo "  Demo complete. All acceptance criteria exercised."
hr
