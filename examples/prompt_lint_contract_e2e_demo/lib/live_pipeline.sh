#!/usr/bin/env bash
# Live LLM pipeline: clarify → generate → test → pytest with artifact snapshots.
#
# Invoked by demo.sh / run_e2e.py --live. Requires API credentials.
# Persists under reports/artifacts/ and reports/diffs/ (reports/ is gitignored).

set -euo pipefail

DEMO_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck disable=SC1091
source "$DEMO_DIR/lib/artifacts.sh"

export PDD_SKIP_UPDATE_CHECK="${PDD_SKIP_UPDATE_CHECK:-1}"
export PDD_ALLOW_DUPLICATE_RUN="${PDD_ALLOW_DUPLICATE_RUN:-1}"

cd "$DEMO_DIR"

CODEGEN_PROMPT="prompts/foo_codegen_python.prompt"
FORMALIZED_PROMPT="prompts/foo_formalized_python.prompt"
VAGUE_PROMPT="prompts/foo_vague_python.prompt"
WORK_PROMPT="prompts/foo_work_python.prompt"
SRC_OUT="src/foo_work.py"
TEST_OUT="tests/test_foo_work.py"

REPORTS="reports"
ARTIFACTS="$REPORTS/artifacts"
DIFFS="$REPORTS/diffs"

pick_python() {
    if command -v python3.12 >/dev/null 2>&1; then
        command -v python3.12
        return
    fi
    command -v python3
}

PY="$(pick_python)"
EXIT_LLM_UNAVAILABLE=77

hdr() { printf '\n%s\n  %s\n%s\n' '================================================================' "$1" '================================================================'; }

llm_configured() {
    "$PY" - <<'PY'
import os, sys
if os.environ.get("PDD_MODEL_DEFAULT"):
    sys.exit(0)
for k in ("OPENAI_API_KEY", "ANTHROPIC_API_KEY", "GEMINI_API_KEY", "GOOGLE_API_KEY", "AZURE_API_KEY", "VERTEXAI_PROJECT"):
    if os.environ.get(k):
        sys.exit(0)
sys.exit(1)
PY
}

llm_preflight() {
    "$PY" - <<'PY'
import os, sys
os.environ.setdefault("PDD_SKIP_UPDATE_CHECK", "1")
try:
    from pdd.llm_invoke import llm_invoke
except Exception as exc:
    print(f"preflight fail: {exc}", file=sys.stderr)
    sys.exit(1)
try:
    r = llm_invoke(prompt="Reply with the single word: ok", input_json={}, strength=0.1, temperature=0.0, verbose=False)
except Exception as exc:
    print(f"preflight fail: {type(exc).__name__}: {exc}", file=sys.stderr)
    sys.exit(1)
if not str(r.get("result", "")).strip():
    print("preflight fail: empty model output", file=sys.stderr)
    sys.exit(1)
print(f"preflight ok via {r.get('model_name', '?')}")
PY
}

parse_clarify_json() {
    local json_path="$1"
    "$PY" - <<'PY' "$json_path"
import json, sys
path = sys.argv[1]
raw = open(path, encoding="utf-8").read().strip()
if not raw:
    print("0 0", end="")
    sys.exit(0)
# CLI may print banners before JSON — find first { or [
for i, ch in enumerate(raw):
    if ch in "{[":
        try:
            payload = json.loads(raw[i:])
            break
        except json.JSONDecodeError:
            continue
else:
    print("0 0", end="")
    sys.exit(0)
guidance = payload.get("guidance", []) if isinstance(payload, dict) else []
g0 = guidance[0] if guidance else {}
amb = len(g0.get("ambiguities", []) or [])
rej = len(g0.get("formalization_rejected", []) or [])
print(f"{amb} {rej}", end="")
PY
}

lint_warn_err() {
    local prompt="$1"
    "$PY" - <<'PY' "$prompt"
import sys
from pathlib import Path
from pdd.prompt_lint import scan_prompt
p = Path(sys.argv[1])
r = scan_prompt(p)
print(f"{r.warn_count} {r.error_count}")
PY
}

write_live_json() {
    local amb="$1" rej="$2" warn_before="$3" warn_after="$4" compile_err="$5" gen_bytes="$6" test_bytes="$7" pytest_pass="$8" hunks_bc="$9" hunks_ca="${10}"
    "$PY" - <<'PY' "$REPORTS/live.json" "$amb" "$rej" "$warn_before" "$warn_after" "$compile_err" "$gen_bytes" "$test_bytes" "$pytest_pass" "$hunks_bc" "$hunks_ca"
import json, sys
out, amb, rej, wb, wa, ce, gb, tb, pp, hbc, hca = sys.argv[1:11]
payload = {
    "mode": "live",
    "pipeline": "bash:lib/live_pipeline.sh",
    "before_lint": {"warn_count": int(wb), "error_count": 0},
    "after_lint": {"warn_count": int(wa), "error_count": 0},
    "clarify": {"ambiguity_count": int(amb), "formalization_rejected_count": int(rej)},
    "contracts_compile": {"error_count": int(ce)},
    "generate": {"path": "src/foo_work.py", "byte_size": int(gb)},
    "test": {"path": "tests/test_foo_work.py", "byte_size": int(tb)},
    "pytest": {"passed": pp == "1"},
    "diffs": {
        "codegen_before_vs_clarified": {
            "path": "reports/diffs/prompt_codegen_before_vs_clarified.diff",
            "hunk_count": int(hbc),
        },
        "codegen_clarified_vs_formalized": {
            "path": "reports/diffs/prompt_codegen_clarified_vs_formalized.diff",
            "hunk_count": int(hca),
        },
    },
    "artifacts": {
        "prompt_codegen_before": "reports/artifacts/prompt_codegen_before.prompt",
        "prompt_codegen_clarified": "reports/artifacts/prompt_codegen_clarified.prompt",
        "prompt_formalized_target": "reports/artifacts/prompt_formalized_target.prompt",
        "src": "reports/artifacts/src/foo_work.py",
        "test": "reports/artifacts/tests/test_foo_work.py",
    },
}
open(out, "w", encoding="utf-8").write(json.dumps(payload, indent=2) + "\n")
PY
}

cleanup_ephemeral() {
    if [[ "${KEEP_ARTIFACTS:-0}" == "1" ]]; then
        echo "  keeping ephemeral work copy, src/, tests/ (KEEP_ARTIFACTS=1)"
        return 0
    fi
    rm -f "$WORK_PROMPT" "$SRC_OUT" "$TEST_OUT"
    for sub in src tests; do
        if [[ -d "$sub" ]] && [[ -z "$(find "$sub" -mindepth 1 -maxdepth 1 2>/dev/null | head -1)" ]]; then
            rmdir "$sub" 2>/dev/null || true
        fi
    done
}

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

if [[ ! -f "$CODEGEN_PROMPT" ]]; then
    echo "ERROR: missing $CODEGEN_PROMPT" >&2
    exit 1
fi

if ! llm_configured; then
    echo "ERROR: --live requires API credentials or PDD_MODEL_DEFAULT" >&2
    exit "$EXIT_LLM_UNAVAILABLE"
fi

hdr "⓪ LLM preflight"
if ! llm_preflight; then
    echo "SKIP: LLM preflight failed (exit $EXIT_LLM_UNAVAILABLE)" >&2
    exit "$EXIT_LLM_UNAVAILABLE"
fi

artifact_init_dirs "$REPORTS"
mkdir -p "$(dirname "$SRC_OUT")" "$(dirname "$TEST_OUT")" prompts

# Work copy for in-place clarify / generate / test.
cp -f "$CODEGEN_PROMPT" "$WORK_PROMPT"

# Live snapshots: codegen BEFORE clarify vs AFTER clarify (not vague vs formalized).
artifact_save "$CODEGEN_PROMPT" "prompt_codegen_before.prompt" "$REPORTS"
artifact_save "$FORMALIZED_PROMPT" "prompt_formalized_target.prompt" "$REPORTS"
# Optional reference: hand-authored vague → formalized (same as deterministic demo).
artifact_save "$VAGUE_PROMPT" "prompt_vague.prompt" "$REPORTS"
artifact_save "$FORMALIZED_PROMPT" "prompt_formalized.prompt" "$REPORTS"
artifact_diff \
    "$ARTIFACTS/prompt_vague.prompt" \
    "$ARTIFACTS/prompt_formalized.prompt" \
    "prompt_vague_vs_formalized.diff" \
    "prompts/foo_vague_python.prompt" \
    "prompts/foo_formalized_python.prompt" \
    "$REPORTS"

hdr "① BEFORE — pdd prompt lint (codegen work copy)"
read -r WARN_BEFORE ERR_BEFORE <<<"$(lint_warn_err "$WORK_PROMPT")"
echo "  lint before clarify: ${WARN_BEFORE} warn, ${ERR_BEFORE} error"

hdr "② pdd prompt lint --ambiguity --apply --contracts --json"
mkdir -p "$REPORTS"
if ! pdd --quiet prompt lint \
    --ambiguity \
    --non-interactive \
    --apply \
    --contracts \
    --json \
    --stories user_stories \
    --tests-dir tests \
    "$WORK_PROMPT" >"$REPORTS/live_clarify.json" 2>&1; then
    :
fi
if [[ ! -s "$REPORTS/live_clarify.json" ]]; then
    echo "SKIP: clarify returned no JSON (exit $EXIT_LLM_UNAVAILABLE)" >&2
    cleanup_ephemeral
    exit "$EXIT_LLM_UNAVAILABLE"
fi
read -r AMB_COUNT REJ_COUNT <<<"$(parse_clarify_json "$REPORTS/live_clarify.json")"
echo "  clarify: ${AMB_COUNT} ambiguity(ies), ${REJ_COUNT} formalization rejection(s)"

artifact_save "$WORK_PROMPT" "prompt_codegen_clarified.prompt" "$REPORTS"

hdr "③ AFTER — pdd prompt lint (clarified work copy)"
read -r WARN_AFTER ERR_AFTER <<<"$(lint_warn_err "$WORK_PROMPT")"
echo "  lint after clarify: ${WARN_AFTER} warn, ${ERR_AFTER} error"

hdr "④ pdd contracts compile --json (clarified)"
pdd --quiet contracts compile --json "$WORK_PROMPT" >"$REPORTS/live_compile.json" 2>&1 || true
COMPILE_ERR="$("$PY" - <<'PY' "$REPORTS/live_compile.json"
import json, sys
raw = open(sys.argv[1], encoding="utf-8").read()
for i, ch in enumerate(raw):
    if ch in "{[":
        try:
            rows = json.loads(raw[i:])
            if not isinstance(rows, list):
                rows = [rows]
            print(sum(int(r.get("error_count", 0) or 0) for r in rows))
            break
        except json.JSONDecodeError:
            pass
else:
    print("0")
PY
)"
echo "  compile errors: ${COMPILE_ERR}"

hdr "⑤ pdd coverage --contracts --json (clarified)"
pdd --quiet coverage --contracts --json \
    --stories-dir user_stories \
    --tests-dir tests \
    "$WORK_PROMPT" >"$REPORTS/live_coverage.json" 2>&1 || true

hdr "⑥ pdd --force generate → src/foo_work.py"
if ! pdd --force generate "$WORK_PROMPT" --output "$SRC_OUT"; then
    echo "ERROR: pdd generate failed" >&2
    cleanup_ephemeral
    exit 1
fi
if [[ ! -s "$SRC_OUT" ]]; then
    echo "SKIP: generate produced empty file (exit $EXIT_LLM_UNAVAILABLE)" >&2
    cleanup_ephemeral
    exit "$EXIT_LLM_UNAVAILABLE"
fi
GEN_BYTES="$(wc -c <"$SRC_OUT" | tr -d ' ')"
artifact_save "$SRC_OUT" "src/foo_work.py" "$REPORTS"
echo "  generated ${GEN_BYTES} bytes"

hdr "⑦ pdd test --manual → tests/test_foo_work.py"
if ! pdd --quiet test --manual "$WORK_PROMPT" "$SRC_OUT" --output "$TEST_OUT"; then
    echo "ERROR: pdd test failed" >&2
    cleanup_ephemeral
    exit 1
fi
if [[ ! -s "$TEST_OUT" ]]; then
    echo "SKIP: test produced empty file (exit $EXIT_LLM_UNAVAILABLE)" >&2
    cleanup_ephemeral
    exit "$EXIT_LLM_UNAVAILABLE"
fi
TEST_BYTES="$(wc -c <"$TEST_OUT" | tr -d ' ')"
artifact_save "$TEST_OUT" "tests/test_foo_work.py" "$REPORTS"
echo "  test file ${TEST_BYTES} bytes"

hdr "⑧ pytest"
if "$PY" -m pytest "$TEST_OUT" -q; then
    PYTEST_PASS=1
    echo "  pytest: PASS"
else
    PYTEST_PASS=0
    echo "  pytest: FAIL" >&2
fi

hdr "⑨ Persist diffs (foo_codegen before/after clarify + distance to formalized)"
artifact_diff \
    "$ARTIFACTS/prompt_codegen_before.prompt" \
    "$ARTIFACTS/prompt_codegen_clarified.prompt" \
    "prompt_codegen_before_vs_clarified.diff" \
    "prompts/foo_codegen_python.prompt (before)" \
    "prompts/foo_work_python.prompt (after clarify)" \
    "$REPORTS"
HUNKS_BC="$(grep -c '^@@' "$DIFFS/prompt_codegen_before_vs_clarified.diff" 2>/dev/null || echo 0)"

artifact_diff \
    "$ARTIFACTS/prompt_codegen_clarified.prompt" \
    "$ARTIFACTS/prompt_formalized_target.prompt" \
    "prompt_codegen_clarified_vs_formalized.diff" \
    "prompt_codegen_clarified.prompt" \
    "prompts/foo_formalized_python.prompt (target)" \
    "$REPORTS"
HUNKS_CA="$(grep -c '^@@' "$DIFFS/prompt_codegen_clarified_vs_formalized.diff" 2>/dev/null || echo 0)"

write_live_json \
    "$AMB_COUNT" "$REJ_COUNT" \
    "$WARN_BEFORE" "$WARN_AFTER" \
    "$COMPILE_ERR" "$GEN_BYTES" "$TEST_BYTES" \
    "$PYTEST_PASS" "$HUNKS_BC" "$HUNKS_CA"

hdr "⑩ Live summary"
echo "  warnings:        ${WARN_BEFORE} → ${WARN_AFTER}"
echo "  ambiguities:     ${AMB_COUNT}"
echo "  compile errors:  ${COMPILE_ERR}"
echo "  generate bytes:  ${GEN_BYTES}"
echo "  test bytes:      ${TEST_BYTES}"
echo "  pytest:          $([[ "$PYTEST_PASS" == "1" ]] && echo PASS || echo FAIL)"
echo "  artifacts:       $ARTIFACTS/"
echo "  diffs:           $DIFFS/prompt_codegen_before_vs_clarified.diff (${HUNKS_BC} hunk(s))"
echo "                   $DIFFS/prompt_codegen_clarified_vs_formalized.diff (${HUNKS_CA} hunk(s))"

FAIL=0
if [[ "$AMB_COUNT" -lt 1 ]]; then
    echo "  FAIL: expected >=1 ambiguity from clarify" >&2
    FAIL=1
fi
if [[ "$WARN_AFTER" -gt "$WARN_BEFORE" ]]; then
    echo "  FAIL: warnings increased after clarify" >&2
    FAIL=1
fi
if [[ "$GEN_BYTES" -le 0 || "$TEST_BYTES" -le 0 ]]; then
    FAIL=1
fi
if [[ "$PYTEST_PASS" != "1" ]]; then
    FAIL=1
fi

cleanup_ephemeral

if [[ "$FAIL" -ne 0 ]]; then
    echo "  Live E2E FAILED" >&2
    exit 1
fi
echo "  Live E2E passed (bash pipeline + real pdd CLI + LLM)."
exit 0
