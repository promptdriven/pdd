#!/usr/bin/env bash
# Experiment B — strict clarify sandwich for cost_tracker.
#
# BEFORE clarify: generate → test → py_compile → pytest → evidence
# CLARIFY: pdd prompt lint --ambiguity --apply --contracts
# AFTER clarify: same stack on clarified work copy
#
# Controls: same generate output path (cost_tracker_utility.py) both arms.

set -euo pipefail

DEMO_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REPO_ROOT="$(cd "$DEMO_DIR/../.." && pwd)"
PARENT_DEMO="$(cd "$DEMO_DIR/../contract_commands_cost_tracker_e2e_demo" && pwd)"

# shellcheck disable=SC1091
source "$DEMO_DIR/scripts/artifacts.sh"

export PDD_SKIP_UPDATE_CHECK="${PDD_SKIP_UPDATE_CHECK:-1}"
export PDD_ALLOW_DUPLICATE_RUN="${PDD_ALLOW_DUPLICATE_RUN:-1}"

cd "$DEMO_DIR"
mkdir -p prompts src/edit_file_tool tests

BASELINE_PROMPT="$PARENT_DEMO/prompts/cost_tracker_utility_Python.prompt"
WORK_PROMPT="prompts/cost_tracker_work_python.prompt"
SRC_CANONICAL="src/edit_file_tool/cost_tracker_utility.py"
SRC_SNAP_BEFORE="src/edit_file_tool/cost_tracker_utility_before.py"
SRC_SNAP_AFTER="src/edit_file_tool/cost_tracker_utility_after.py"
TEST_BEFORE="tests/test_cost_tracker_work_before.py"
TEST_AFTER="tests/test_cost_tracker_work_after.py"

REPORTS="reports"
ARTIFACTS="$REPORTS/artifacts"
DIFFS="$REPORTS/diffs"
STORIES_DIR="$PARENT_DEMO/user_stories"
TESTS_DIR="$PARENT_DEMO/tests"
GOLDEN_TEST="$PARENT_DEMO/tests/test_cost_tracker_reference.py"
export GOLDEN_TEST

resolve_runtime() {
    # Prefer repo .venv so PY and PDD share the same editable install.
    if [[ -x "$REPO_ROOT/.venv/bin/python" ]]; then
        if "$REPO_ROOT/.venv/bin/python" -c "from pdd.generate_test import finalize_python_test_content" 2>/dev/null; then
            PY="$REPO_ROOT/.venv/bin/python"
            PDD="$REPO_ROOT/.venv/bin/pdd"
            return 0
        fi
    fi
    if command -v python3.12 >/dev/null 2>&1; then
        PY="$(command -v python3.12)"
    else
        PY="$(command -v python3)"
    fi
    if [[ -x "$REPO_ROOT/.venv/bin/pdd" ]]; then
        PDD="$REPO_ROOT/.venv/bin/pdd"
    elif command -v pdd >/dev/null 2>&1; then
        PDD="$(command -v pdd)"
    else
        echo "ERROR: pdd not found; run: pip install -e $REPO_ROOT" >&2
        return 1
    fi
    if ! "$PY" -c "from pdd.generate_test import finalize_python_test_content" 2>/dev/null; then
        echo "ERROR: active Python cannot import pdd from $REPO_ROOT" >&2
        echo "  Fix: pip install -e $REPO_ROOT" >&2
        echo "  Then use: $REPO_ROOT/.venv/bin/python (or conda env with editable install)" >&2
        echo "  pdd on PATH: $PDD" >&2
        return 1
    fi
}

PY=""
PDD=""
resolve_runtime || exit 1
echo "  using python: $PY"
echo "  using pdd: $PDD"

EXIT_LLM_UNAVAILABLE=77
export GENERATE_OUTPUT="$SRC_CANONICAL"

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
from pdd.llm_invoke import llm_invoke
r = llm_invoke(prompt="Reply with the single word: ok", input_json={}, strength=0.1, temperature=0.0, verbose=False)
if not str(r.get("result", "")).strip():
    sys.exit(1)
print(r.get("model_name", "?"))
PY
}

parse_clarify_json() {
    "$PY" - <<'PY' "$1"
import json, sys
raw = open(sys.argv[1], encoding="utf-8").read().strip()
if not raw:
    print("0 0"); sys.exit(0)
for i, ch in enumerate(raw):
    if ch in "{[":
        try:
            payload = json.loads(raw[i:])
            break
        except json.JSONDecodeError:
            continue
else:
    print("0 0"); sys.exit(0)
guidance = payload.get("guidance", []) if isinstance(payload, dict) else []
g0 = guidance[0] if guidance else {}
print(f"{len(g0.get('ambiguities', []) or [])} {len(g0.get('formalization_rejected', []) or [])}")
PY
}

lint_warn_err() {
    "$PY" - <<'PY' "$1"
import sys
from pathlib import Path
from pdd.prompt_lint import scan_prompt
r = scan_prompt(Path(sys.argv[1]))
print(f"{r.warn_count} {r.error_count}")
PY
}

coverage_summary_from_evidence() {
    "$PY" - <<'PY' "$1"
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
rows = d.get("coverage", {}).get("results", [])
if not rows:
    print("0 0 0")
else:
    s = rows[0].get("summary", {}) or {}
    print(s.get("unchecked", 0), s.get("checked", 0), s.get("total", 0))
PY
}

run_golden_export() {
    local src_snap="$1"
    local suffix="$2"
    local result
    result="$("$PY" "$DEMO_DIR/scripts/run_golden_pytest.py" "$src_snap" "$GOLDEN_TEST" --json 2>/dev/null)" || result='{"exit_ok":false,"passed":0,"failed":1}'
    local ok passed failed
    ok="$("$PY" - <<'PY' "$result"
import json, sys
r = json.loads(sys.argv[1])
print("1" if r.get("exit_ok") else "0", r.get("passed", 0), r.get("failed", 0))
PY
)"
    read -r ok passed failed <<<"$ok"
    eval "GOLDEN_${suffix}=\$ok"
    eval "GOLDEN_PASSED_${suffix}=\$passed"
    eval "GOLDEN_FAILED_${suffix}=\$failed"
    echo "  golden pytest (${suffix}): $([[ "$ok" == "1" ]] && echo PASS || echo FAIL) ${passed} passed, ${failed} failed"
}

markers_missing_count() {
    local test_file="$1"
    local prompt_path="$2"
    "$PY" - <<'PY' "$test_file" "$prompt_path"
import re
import sys
from pathlib import Path
test = Path(sys.argv[1])
prompt = Path(sys.argv[2])
text = test.read_text(encoding="utf-8") if test.is_file() else ""
rules = set(re.findall(r"\bR(\d+)\b", prompt.read_text(encoding="utf-8")))
found = set()
for m in re.finditer(r"test_R(\d+)_", text):
    found.add(m.group(1))
for m in re.finditer(r"#\s*R(\d+):", text):
    found.add(m.group(1))
missing = [f"R{r}" for r in sorted(rules, key=int) if r not in found] if rules else []
print(len(missing))
PY
}

sha256_file() {
    "$PY" - <<'PY' "$1"
import hashlib, sys
h = hashlib.sha256()
with open(sys.argv[1], "rb") as f:
    for chunk in iter(lambda: f.read(65536), b""):
        h.update(chunk)
print(h.hexdigest())
PY
}

# Run generate → test → py_compile → pytest; sets GEN_BYTES_* TEST_BYTES_* SYNTAX_* PYTEST_* PYTEST_PASSED_* ...
run_codegen_stack() {
    local phase="$1"
    local prompt_path="$2"
    local src_path="$3"
    local test_path="$4"
    local suffix="$5"

    mkdir -p "$(dirname "$src_path")" "$(dirname "$test_path")"

    hdr "${phase} — pdd --force generate → ${SRC_CANONICAL}"
    if ! "$PDD" --force generate "$prompt_path" --output "$SRC_CANONICAL"; then
        echo "ERROR: generate failed (${phase})" >&2
        return 1
    fi
    if [[ ! -s "$SRC_CANONICAL" ]]; then
        return "$EXIT_LLM_UNAVAILABLE"
    fi
    cp -f "$SRC_CANONICAL" "$src_path"
    local gen_bytes
    gen_bytes="$(wc -c <"$SRC_CANONICAL" | tr -d ' ')"
    eval "GEN_BYTES_${suffix}=\$gen_bytes"
    artifact_save "$SRC_CANONICAL" "src/$(basename "$src_path")" "$REPORTS"
    echo "  generated ${gen_bytes} bytes; snapshot → ${src_path}"

    hdr "${phase} — pdd --force test --manual"
    if ! "$PDD" --quiet --force test --manual "$prompt_path" "$SRC_CANONICAL" --output "$test_path"; then
        echo "ERROR: test failed (${phase})" >&2
        return 1
    fi
    if [[ ! -s "$test_path" ]]; then
        return "$EXIT_LLM_UNAVAILABLE"
    fi
    local test_bytes
    test_bytes="$(wc -c <"$test_path" | tr -d ' ')"
    eval "TEST_BYTES_${suffix}=\$test_bytes"
    artifact_save "$test_path" "tests/$(basename "$test_path")" "$REPORTS"
    echo "  test ${test_bytes} bytes → ${test_path}"

    if "$PY" -m py_compile "$SRC_CANONICAL" "$test_path" 2>/dev/null; then
        eval "SYNTAX_${suffix}=1"
        echo "  py_compile: OK"
    else
        eval "SYNTAX_${suffix}=0"
        echo "  py_compile: FAIL" >&2
    fi

    eval "PYTEST_PASSED_${suffix}=0"
    eval "PYTEST_FAILED_${suffix}=0"
    eval "PYTEST_${suffix}=0"
    local syntax_ok=0
    eval "syntax_ok=\$SYNTAX_${suffix}"
    if [[ "$syntax_ok" == "1" ]]; then
        hdr "${phase} — pytest ${test_path}"
        local pytest_out passed=0 failed=0
        pytest_out="$(cd "$DEMO_DIR" && PYTHONPATH=src "$PY" -m pytest "$test_path" -q --tb=no 2>&1)" || true
        echo "$pytest_out"
        if echo "$pytest_out" | grep -qE '[0-9]+ passed'; then
            passed="$(echo "$pytest_out" | grep -oE '[0-9]+ passed' | head -1 | awk '{print $1}')"
        fi
        if echo "$pytest_out" | grep -qE '[0-9]+ failed'; then
            failed="$(echo "$pytest_out" | grep -oE '[0-9]+ failed' | head -1 | awk '{print $1}')"
        fi
        eval "PYTEST_PASSED_${suffix}=\$passed"
        eval "PYTEST_FAILED_${suffix}=\$failed"
        if (cd "$DEMO_DIR" && PYTHONPATH=src "$PY" -m pytest "$test_path" -q --tb=no >/dev/null 2>&1); then
            eval "PYTEST_${suffix}=1"
            echo "  pytest: PASS (${passed} passed)"
        else
            echo "  pytest: FAIL (${passed} passed, ${failed} failed)" >&2
        fi
    else
        echo "  pytest: SKIP (syntax error)" >&2
    fi
    return 0
}

emit_evidence() {
    local prompt_path="$1"
    local out_json="$2"
    "$PDD" --quiet evidence emit \
        --prompt "$prompt_path" \
        --output "$out_json" \
        --stories-dir "$STORIES_DIR" \
        --tests-dir "$TESTS_DIR" || true
}

cleanup_ephemeral() {
    if [[ "${KEEP_ARTIFACTS:-0}" == "1" ]]; then
        echo "  keeping ephemeral files (KEEP_ARTIFACTS=1)"
        return 0
    fi
    rm -f "$WORK_PROMPT" "$TEST_BEFORE" "$TEST_AFTER"
    rm -f "$SRC_CANONICAL" "$SRC_SNAP_BEFORE" "$SRC_SNAP_AFTER"
    for sub in src tests; do
        if [[ -d "$sub" ]] && [[ -z "$(find "$sub" -mindepth 1 -maxdepth 1 2>/dev/null | head -1)" ]]; then
            rmdir "$sub" 2>/dev/null || true
        fi
    done
}

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

if [[ ! -f "$BASELINE_PROMPT" ]]; then
    echo "ERROR: missing $BASELINE_PROMPT" >&2
    exit 1
fi

if ! llm_configured; then
    echo "ERROR: --live-ab requires API credentials or PDD_MODEL_DEFAULT" >&2
    exit "$EXIT_LLM_UNAVAILABLE"
fi

hdr "⓪ LLM preflight"
PREFLIGHT_MODEL="$(llm_preflight)" || {
    echo "SKIP: LLM preflight failed" >&2
    exit "$EXIT_LLM_UNAVAILABLE"
}
echo "  preflight ok via ${PREFLIGHT_MODEL}"
export PREFLIGHT_MODEL

PDD_VERSION="$("$PY" -c "import pdd; print(getattr(pdd, '__version__', '?'))" 2>/dev/null || echo "?")"
export PDD_VERSION

artifact_init_dirs "$REPORTS"
cp -f "$BASELINE_PROMPT" "$WORK_PROMPT"
artifact_save "$WORK_PROMPT" "prompt_pre_clarify.prompt" "$REPORTS"
export SHA_PRE="$(sha256_file "$WORK_PROMPT")"

hdr "① Lint BEFORE clarify"
read -r WARN_BEFORE ERR_BEFORE <<<"$(lint_warn_err "$WORK_PROMPT")"
echo "  ${WARN_BEFORE} warn, ${ERR_BEFORE} error"

GEN_BYTES_BEFORE=0 TEST_BYTES_BEFORE=0 SYNTAX_BEFORE=0 PYTEST_BEFORE=0
PYTEST_PASSED_BEFORE=0 PYTEST_FAILED_BEFORE=0
if ! run_codegen_stack "② BEFORE clarify" "$WORK_PROMPT" "$SRC_SNAP_BEFORE" "$TEST_BEFORE" BEFORE; then
    rc=$?
    cleanup_ephemeral
    exit "$rc"
fi

hdr "②b Golden tests on BEFORE src snapshot (primary code metric)"
run_golden_export "$SRC_SNAP_BEFORE" BEFORE
export MARKERS_MISSING_BEFORE="$(markers_missing_count "$TEST_BEFORE" "$WORK_PROMPT")"
echo "  contract markers missing (generated test): ${MARKERS_MISSING_BEFORE}"

hdr "③ Evidence BEFORE clarify"
EVIDENCE_PRE="$REPORTS/evidence_pre_clarify.json"
emit_evidence "$WORK_PROMPT" "$EVIDENCE_PRE"
export EVIDENCE_PRE

read -r UNCHECKED_BEFORE COVERAGE_CHECKED_BEFORE COVERAGE_TOTAL_BEFORE <<<"$(coverage_summary_from_evidence "$EVIDENCE_PRE")"
export UNCHECKED_BEFORE COVERAGE_CHECKED_BEFORE COVERAGE_TOTAL_BEFORE

hdr "④ CLARIFY — pdd prompt lint --ambiguity --apply --contracts --json"
if ! "$PDD" --quiet prompt lint \
    --ambiguity --non-interactive --apply --contracts --json \
    --stories "$STORIES_DIR" --tests-dir "$TESTS_DIR" \
    "$WORK_PROMPT" >"$REPORTS/live_clarify.json" 2>&1; then
    :
fi
if [[ ! -s "$REPORTS/live_clarify.json" ]]; then
    cleanup_ephemeral
    exit "$EXIT_LLM_UNAVAILABLE"
fi
read -r AMB_COUNT REJ_COUNT <<<"$(parse_clarify_json "$REPORTS/live_clarify.json")"
echo "  ${AMB_COUNT} ambiguity(ies), ${REJ_COUNT} rejection(s)"
export AMB_COUNT REJ_COUNT

artifact_save "$WORK_PROMPT" "prompt_post_clarify.prompt" "$REPORTS"
export SHA_POST="$(sha256_file "$WORK_PROMPT")"

hdr "⑤ Lint AFTER clarify"
read -r WARN_AFTER ERR_AFTER <<<"$(lint_warn_err "$WORK_PROMPT")"
echo "  ${WARN_AFTER} warn, ${ERR_AFTER} error"

hdr "⑥ contracts compile + coverage"
"$PDD" --quiet contracts compile --json "$WORK_PROMPT" >"$REPORTS/live_compile.json" 2>&1 || true
COMPILE_ERR="$("$PY" - <<'PY' "$REPORTS/live_compile.json"
import json, sys
raw = open(sys.argv[1], encoding="utf-8").read()
for i, ch in enumerate(raw):
    if ch in "{[":
        try:
            rows = json.loads(raw[i:])
            if not isinstance(rows, list): rows = [rows]
            print(sum(int(r.get("error_count", 0) or 0) for r in rows))
            break
        except json.JSONDecodeError:
            pass
else:
    print("0")
PY
)"
RULE_COUNT_AFTER="$("$PY" - <<'PY' "$REPORTS/live_compile.json"
import json, sys
raw = open(sys.argv[1], encoding="utf-8").read()
for i, ch in enumerate(raw):
    if ch in "{[":
        try:
            rows = json.loads(raw[i:])
            if not isinstance(rows, list): rows = [rows]
            print(sum(len(r.get("rules", []) or []) for r in rows))
            break
        except json.JSONDecodeError:
            pass
else:
    print("0")
PY
)"
"$PDD" --quiet coverage --contracts --json \
    --stories-dir "$STORIES_DIR" --tests-dir "$TESTS_DIR" \
    "$WORK_PROMPT" >"$REPORTS/live_coverage.json" 2>&1 || true
UNCHECKED_AFTER="$("$PY" - <<'PY' "$REPORTS/live_coverage.json"
import json, sys
raw = open(sys.argv[1], encoding="utf-8").read()
for i, ch in enumerate(raw):
    if ch in "{[":
        try:
            payload = json.loads(raw[i:])
            rows = payload.get("results", []) if isinstance(payload, dict) else payload
            print(rows[0].get("summary", {}).get("unchecked", 0) if rows else 0)
            break
        except json.JSONDecodeError:
            pass
else:
    print("0")
PY
)"
export COMPILE_ERR RULE_COUNT_AFTER UNCHECKED_AFTER
export COVERAGE_TOTAL_AFTER="$("$PY" - <<'PY' "$REPORTS/live_coverage.json"
import json, sys
raw = open(sys.argv[1], encoding="utf-8").read()
for i, ch in enumerate(raw):
    if ch in "{[":
        try:
            rows = json.loads(raw[i:]).get("results", []) if isinstance(json.loads(raw[i:]), dict) else json.loads(raw[i:])
            if not isinstance(rows, list):
                rows = [rows]
            print(rows[0].get("summary", {}).get("total", 0) if rows else 0)
            break
        except json.JSONDecodeError:
            pass
else:
    print("0")
PY
)"

hdr "⑦ Evidence AFTER clarify"
EVIDENCE_POST="$REPORTS/evidence_post_clarify.json"
emit_evidence "$WORK_PROMPT" "$EVIDENCE_POST"
export EVIDENCE_POST

hdr "⑧ contracts drift (evidence pre vs post)"
DRIFT_JSON="$("$PDD" --quiet contracts drift --json "$EVIDENCE_PRE" "$EVIDENCE_POST" 2>&1 || true)"
echo "$DRIFT_JSON" >"$REPORTS/drift_evidence.json"
DRIFT_HAS="$("$PY" - <<'PY' "$REPORTS/drift_evidence.json"
import json, sys
raw = open(sys.argv[1], encoding="utf-8").read()
for i, ch in enumerate(raw):
    if ch in "{[":
        try:
            d = json.loads(raw[i:])
            print("true" if d.get("has_drift") else "false")
            print(len(d.get("findings", [])))
            break
        except json.JSONDecodeError:
            pass
else:
    print("false"); print("0")
PY
)"
read -r DRIFT_HAS DRIFT_FINDINGS <<<"$DRIFT_HAS"
export DRIFT_HAS DRIFT_FINDINGS

GEN_BYTES_AFTER=0 TEST_BYTES_AFTER=0 SYNTAX_AFTER=0 PYTEST_AFTER=0
PYTEST_PASSED_AFTER=0 PYTEST_FAILED_AFTER=0
if ! run_codegen_stack "⑨ AFTER clarify" "$WORK_PROMPT" "$SRC_SNAP_AFTER" "$TEST_AFTER" AFTER; then
    rc=$?
    cleanup_ephemeral
    exit "$rc"
fi

hdr "⑨b Golden tests on AFTER src snapshot (primary code metric)"
run_golden_export "$SRC_SNAP_AFTER" AFTER
export MARKERS_MISSING_AFTER="$(markers_missing_count "$TEST_AFTER" "$WORK_PROMPT")"
echo "  contract markers missing (generated test): ${MARKERS_MISSING_AFTER}"

read -r _u COVERAGE_CHECKED_AFTER COVERAGE_TOTAL_POST <<<"$(coverage_summary_from_evidence "$EVIDENCE_POST")"
export COVERAGE_CHECKED_AFTER COVERAGE_TOTAL_AFTER="${COVERAGE_TOTAL_POST:-$COVERAGE_TOTAL_AFTER}"

hdr "⑩ Persist diffs"
artifact_diff \
    "$ARTIFACTS/prompt_pre_clarify.prompt" \
    "$ARTIFACTS/prompt_post_clarify.prompt" \
    "prompt_pre_vs_post.diff" \
    "prompt (pre-clarify)" \
    "prompt (post-clarify)" \
    "$REPORTS"
HUNKS_PROMPT="$(grep -c '^@@' "$DIFFS/prompt_pre_vs_post.diff" 2>/dev/null || echo 0)"

artifact_diff \
    "$ARTIFACTS/src/cost_tracker_utility_before.py" \
    "$ARTIFACTS/src/cost_tracker_utility_after.py" \
    "src_before_vs_after.diff" \
    "src (before)" \
    "src (after)" \
    "$REPORTS"
HUNKS_SRC="$(grep -c '^@@' "$DIFFS/src_before_vs_after.diff" 2>/dev/null || echo 0)"

artifact_diff \
    "$ARTIFACTS/tests/test_cost_tracker_work_before.py" \
    "$ARTIFACTS/tests/test_cost_tracker_work_after.py" \
    "tests_before_vs_after.diff" \
    "tests (before)" \
    "tests (after)" \
    "$REPORTS"
HUNKS_TEST="$(grep -c '^@@' "$DIFFS/tests_before_vs_after.diff" 2>/dev/null || echo 0)"

export HUNKS_PROMPT HUNKS_SRC HUNKS_TEST
export WARN_BEFORE WARN_AFTER
export GEN_BYTES_BEFORE GEN_BYTES_AFTER TEST_BYTES_BEFORE TEST_BYTES_AFTER
export SYNTAX_BEFORE SYNTAX_AFTER PYTEST_BEFORE PYTEST_AFTER
export PYTEST_PASSED_BEFORE PYTEST_FAILED_BEFORE PYTEST_PASSED_AFTER PYTEST_FAILED_AFTER
export GOLDEN_BEFORE GOLDEN_AFTER GOLDEN_PASSED_BEFORE GOLDEN_FAILED_BEFORE
export GOLDEN_PASSED_AFTER GOLDEN_FAILED_AFTER
export MARKERS_MISSING_BEFORE MARKERS_MISSING_AFTER
export COVERAGE_CHECKED_BEFORE COVERAGE_CHECKED_AFTER COVERAGE_TOTAL_AFTER
export PDD_MODEL_DEFAULT="${PDD_MODEL_DEFAULT:-}"

"$PY" "$DEMO_DIR/scripts/write_ab_report.py" "$REPORTS/ab_live.json"

hdr "⑪ Summary"
echo "  lint warns:     ${WARN_BEFORE} → ${WARN_AFTER}"
echo "  ambiguities:    ${AMB_COUNT}"
echo "  compile errors: ${COMPILE_ERR}"
echo "  rules:          ${RULE_COUNT_AFTER}  unchecked: ${UNCHECKED_AFTER}"
echo "  src bytes:      ${GEN_BYTES_BEFORE} → ${GEN_BYTES_AFTER}"
echo "  test bytes:     ${TEST_BYTES_BEFORE} → ${TEST_BYTES_AFTER}"
echo "  py_compile:     $([[ "$SYNTAX_BEFORE" == "1" ]] && echo OK || echo FAIL) → $([[ "$SYNTAX_AFTER" == "1" ]] && echo OK || echo FAIL)"
echo "  gen pytest:     $([[ "$PYTEST_BEFORE" == "1" ]] && echo PASS || echo FAIL) → $([[ "$PYTEST_AFTER" == "1" ]] && echo PASS || echo FAIL)"
echo "  golden pytest:  $([[ "$GOLDEN_BEFORE" == "1" ]] && echo PASS || echo FAIL) → $([[ "$GOLDEN_AFTER" == "1" ]] && echo PASS || echo FAIL)"
echo "  report:         $REPORTS/ab_live.json"

FAIL=0
if [[ "$AMB_COUNT" -lt 1 ]]; then
    echo "  FAIL: expected >=1 ambiguity" >&2
    FAIL=1
fi
if [[ "$WARN_AFTER" -gt "$WARN_BEFORE" ]]; then
    echo "  FAIL: lint warnings increased" >&2
    FAIL=1
fi
if [[ "$GEN_BYTES_BEFORE" -le 0 || "$GEN_BYTES_AFTER" -le 0 ]]; then
    echo "  FAIL: empty generate output" >&2
    FAIL=1
fi
# Primary behavioral gate: shared golden tests (not LLM-generated tests).
if [[ "$GOLDEN_AFTER" -lt "$GOLDEN_BEFORE" ]]; then
    echo "  FAIL: golden pytest regressed (primary code metric)" >&2
    FAIL=1
fi
if [[ "$GOLDEN_FAILED_AFTER" -gt "$GOLDEN_FAILED_BEFORE" ]]; then
    echo "  FAIL: golden test failures increased" >&2
    FAIL=1
fi
# Secondary: generated-test pytest (no regression when syntax OK).
if [[ "$SYNTAX_AFTER" == "1" && "$PYTEST_AFTER" -lt "$PYTEST_BEFORE" ]]; then
    echo "  WARN: generated-test pytest regressed (secondary metric)" >&2
fi

cleanup_ephemeral

if [[ "$FAIL" -ne 0 ]]; then
    exit 1
fi
echo "  Experiment B passed."
exit 0
