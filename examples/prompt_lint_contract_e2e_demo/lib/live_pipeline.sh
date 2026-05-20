#!/usr/bin/env bash
# Live LLM pipeline: codegen BEFORE clarify (generate/test/pytest) → clarify → AFTER stack.
#
# Compares prompt lint, Python src, pytest files, and pass rates on both sides of
# ``pdd prompt lint --ambiguity --apply --contracts``.
#
# Invoked by demo.sh / run_e2e.py --live. Requires API credentials.
# Persists under reports/artifacts/ and reports/diffs/ (reports/ is gitignored).

set -euo pipefail

DEMO_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REPO_ROOT="$(cd "$DEMO_DIR/../.." && pwd)"
# shellcheck disable=SC1091
source "$DEMO_DIR/lib/artifacts.sh"

export PDD_SKIP_UPDATE_CHECK="${PDD_SKIP_UPDATE_CHECK:-1}"
export PDD_ALLOW_DUPLICATE_RUN="${PDD_ALLOW_DUPLICATE_RUN:-1}"

cd "$DEMO_DIR"

CODEGEN_PROMPT="prompts/foo_codegen_python.prompt"
FORMALIZED_PROMPT="prompts/foo_formalized_python.prompt"
VAGUE_PROMPT="prompts/foo_vague_python.prompt"
WORK_PROMPT="prompts/foo_work_python.prompt"

SRC_BEFORE="src/foo_work_before.py"
SRC_AFTER="src/foo_work_after.py"
TEST_BEFORE="tests/test_foo_work_before.py"
TEST_AFTER="tests/test_foo_work_after.py"

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

if [[ -x "$REPO_ROOT/.venv/bin/pdd" ]]; then
    PDD="$REPO_ROOT/.venv/bin/pdd"
elif command -v pdd >/dev/null 2>&1; then
    PDD="$(command -v pdd)"
else
    echo "ERROR: pdd not found; run: pip install -e $REPO_ROOT" >&2
    exit 1
fi
if ! "$PY" -c "from pdd.generate_test import finalize_python_test_content" 2>/dev/null; then
    echo "ERROR: active Python cannot import finalize_python_test_content; run:" >&2
    echo "  pip install -e $REPO_ROOT" >&2
    echo "  pdd binary: $PDD" >&2
    exit 1
fi
echo "  using pdd: $PDD"

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

# Run generate → test → py_compile → pytest for one prompt/code stack.
# Sets GEN_BYTES_* / TEST_BYTES_* / SYNTAX_* / PYTEST_* globals via suffix (before|after).
run_codegen_stack() {
    local phase="$1"
    local prompt_path="$2"
    local src_path="$3"
    local test_path="$4"
    local suffix="$5"

    mkdir -p "$(dirname "$src_path")" "$(dirname "$test_path")"

    hdr "${phase} — pdd --force generate → ${src_path}"
    if ! "$PDD" --force generate "$prompt_path" --output "$src_path"; then
        echo "ERROR: pdd generate failed (${phase})" >&2
        return 1
    fi
    if [[ ! -s "$src_path" ]]; then
        echo "SKIP: generate produced empty file (${phase})" >&2
        return "$EXIT_LLM_UNAVAILABLE"
    fi
    local gen_bytes test_bytes
    gen_bytes="$(wc -c <"$src_path" | tr -d ' ')"
    eval "GEN_BYTES_${suffix}=\$gen_bytes"
    artifact_save "$src_path" "src/$(basename "$src_path")" "$REPORTS"
    echo "  generated ${gen_bytes} bytes → ${src_path}"

    hdr "${phase} — pdd test --manual → ${test_path}"
    if ! "$PDD" --quiet --force test --manual "$prompt_path" "$src_path" --output "$test_path"; then
        echo "ERROR: pdd test failed (${phase})" >&2
        return 1
    fi
    if [[ ! -s "$test_path" ]]; then
        echo "SKIP: test produced empty file (${phase})" >&2
        return "$EXIT_LLM_UNAVAILABLE"
    fi
    test_bytes="$(wc -c <"$test_path" | tr -d ' ')"
    eval "TEST_BYTES_${suffix}=\$test_bytes"
    artifact_save "$test_path" "tests/$(basename "$test_path")" "$REPORTS"
    echo "  test file ${test_bytes} bytes → ${test_path}"

    if "$PY" -m py_compile "$test_path" 2>/dev/null; then
        eval "SYNTAX_${suffix}=1"
        echo "  py_compile: OK"
    else
        eval "SYNTAX_${suffix}=0"
        echo "  py_compile: FAIL (invalid Python — pytest will not collect)" >&2
    fi

    hdr "${phase} — pytest ${test_path}"
    local syntax_ok=0
    eval "syntax_ok=\$SYNTAX_${suffix}"
    if [[ "$syntax_ok" == "1" ]]; then
        local pytest_out passed=0 failed=0
        pytest_out="$("$PY" -m pytest "$test_path" -q --tb=no 2>&1)" || true
        echo "$pytest_out"
        if echo "$pytest_out" | grep -qE '[0-9]+ passed'; then
            passed="$(echo "$pytest_out" | grep -oE '[0-9]+ passed' | head -1 | awk '{print $1}')"
        fi
        if echo "$pytest_out" | grep -qE '[0-9]+ failed'; then
            failed="$(echo "$pytest_out" | grep -oE '[0-9]+ failed' | head -1 | awk '{print $1}')"
        fi
        if "$PY" -m pytest "$test_path" -q --tb=no >/dev/null 2>&1; then
            eval "PYTEST_${suffix}=1"
            echo "  pytest: PASS (${passed} passed)"
            return 0
        fi
        eval "PYTEST_${suffix}=0"
        echo "  pytest: FAIL (${passed} passed, ${failed} failed)" >&2
        return 0
    fi
    eval "PYTEST_${suffix}=0"
    echo "  pytest: SKIP (syntax error)" >&2
    return 0
}

write_live_json() {
    "$PY" - <<'PY' \
        "$REPORTS/live.json" \
        "$AMB_COUNT" "$REJ_COUNT" \
        "$WARN_BEFORE" "$WARN_AFTER" \
        "$COMPILE_ERR" \
        "$GEN_BYTES_BEFORE" "$GEN_BYTES_AFTER" \
        "$TEST_BYTES_BEFORE" "$TEST_BYTES_AFTER" \
        "$SYNTAX_BEFORE" "$SYNTAX_AFTER" \
        "$PYTEST_BEFORE" "$PYTEST_AFTER" \
        "$HUNKS_BC" "$HUNKS_CA" "$HUNKS_SRC" "$HUNKS_TEST"
import json, sys
(
    out, amb, rej, wb, wa, ce,
    gb_b, gb_a, tb_b, tb_a, syn_b, syn_a, pyt_b, pyt_a,
    hbc, hca, hsrc, htest,
) = sys.argv[1:19]
payload = {
    "mode": "live",
    "pipeline": "bash:lib/live_pipeline.sh",
    "before_lint": {"warn_count": int(wb), "error_count": 0},
    "after_lint": {"warn_count": int(wa), "error_count": 0},
    "clarify": {"ambiguity_count": int(amb), "formalization_rejected_count": int(rej)},
    "contracts_compile": {"error_count": int(ce)},
    "before": {
        "prompt": "prompts/foo_work_python.prompt (pre-clarify copy of foo_codegen)",
        "generate": {"path": "src/foo_work_before.py", "byte_size": int(gb_b)},
        "test": {"path": "tests/test_foo_work_before.py", "byte_size": int(tb_b)},
        "py_compile_ok": syn_b == "1",
        "pytest": {"passed": pyt_b == "1"},
    },
    "after": {
        "prompt": "prompts/foo_work_python.prompt (post-clarify)",
        "generate": {"path": "src/foo_work_after.py", "byte_size": int(gb_a)},
        "test": {"path": "tests/test_foo_work_after.py", "byte_size": int(tb_a)},
        "py_compile_ok": syn_a == "1",
        "pytest": {"passed": pyt_a == "1"},
    },
    "diffs": {
        "prompt_codegen_before_vs_clarified": {
            "path": "reports/diffs/prompt_codegen_before_vs_clarified.diff",
            "hunk_count": int(hbc),
        },
        "prompt_codegen_clarified_vs_formalized": {
            "path": "reports/diffs/prompt_codegen_clarified_vs_formalized.diff",
            "hunk_count": int(hca),
        },
        "src_before_vs_after": {
            "path": "reports/diffs/src_before_vs_after.diff",
            "hunk_count": int(hsrc),
        },
        "tests_before_vs_after": {
            "path": "reports/diffs/tests_before_vs_after.diff",
            "hunk_count": int(htest),
        },
    },
    "artifacts": {
        "prompt_codegen_before": "reports/artifacts/prompt_codegen_before.prompt",
        "prompt_codegen_clarified": "reports/artifacts/prompt_codegen_clarified.prompt",
        "prompt_formalized_target": "reports/artifacts/prompt_formalized_target.prompt",
        "src_before": "reports/artifacts/src/foo_work_before.py",
        "src_after": "reports/artifacts/src/foo_work_after.py",
        "test_before": "reports/artifacts/tests/test_foo_work_before.py",
        "test_after": "reports/artifacts/tests/test_foo_work_after.py",
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
    rm -f \
        "$WORK_PROMPT" \
        "$SRC_BEFORE" "$SRC_AFTER" \
        "$TEST_BEFORE" "$TEST_AFTER" \
        src/foo_work.py tests/test_foo_work.py
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
mkdir -p prompts src tests

cp -f "$CODEGEN_PROMPT" "$WORK_PROMPT"

artifact_save "$CODEGEN_PROMPT" "prompt_codegen_before.prompt" "$REPORTS"
artifact_save "$FORMALIZED_PROMPT" "prompt_formalized_target.prompt" "$REPORTS"
artifact_save "$VAGUE_PROMPT" "prompt_vague.prompt" "$REPORTS"
artifact_save "$FORMALIZED_PROMPT" "prompt_formalized.prompt" "$REPORTS"
artifact_diff \
    "$ARTIFACTS/prompt_vague.prompt" \
    "$ARTIFACTS/prompt_formalized.prompt" \
    "prompt_vague_vs_formalized.diff" \
    "prompts/foo_vague_python.prompt" \
    "prompts/foo_formalized_python.prompt" \
    "$REPORTS"

hdr "① BEFORE clarify — pdd prompt lint (codegen work copy)"
read -r WARN_BEFORE ERR_BEFORE <<<"$(lint_warn_err "$WORK_PROMPT")"
echo "  lint before clarify: ${WARN_BEFORE} warn, ${ERR_BEFORE} error"

GEN_BYTES_BEFORE=0
TEST_BYTES_BEFORE=0
SYNTAX_BEFORE=0
PYTEST_BEFORE=0
if ! run_codegen_stack \
    "② BEFORE clarify" \
    "$WORK_PROMPT" \
    "$SRC_BEFORE" \
    "$TEST_BEFORE" \
    BEFORE; then
    rc=$?
    cleanup_ephemeral
    exit "$rc"
fi

hdr "③ CLARIFY — pdd prompt lint --ambiguity --apply --contracts --json"
mkdir -p "$REPORTS"
if ! "$PDD" --quiet prompt lint \
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

hdr "④ AFTER clarify — pdd prompt lint (clarified work copy)"
read -r WARN_AFTER ERR_AFTER <<<"$(lint_warn_err "$WORK_PROMPT")"
echo "  lint after clarify: ${WARN_AFTER} warn, ${ERR_AFTER} error"

hdr "⑤ pdd contracts compile --json (clarified)"
"$PDD" --quiet contracts compile --json "$WORK_PROMPT" >"$REPORTS/live_compile.json" 2>&1 || true
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

hdr "⑥ pdd coverage --contracts --json (clarified)"
"$PDD" --quiet coverage --contracts --json \
    --stories-dir user_stories \
    --tests-dir tests \
    "$WORK_PROMPT" >"$REPORTS/live_coverage.json" 2>&1 || true

GEN_BYTES_AFTER=0
TEST_BYTES_AFTER=0
SYNTAX_AFTER=0
PYTEST_AFTER=0
if ! run_codegen_stack \
    "⑦ AFTER clarify" \
    "$WORK_PROMPT" \
    "$SRC_AFTER" \
    "$TEST_AFTER" \
    AFTER; then
    rc=$?
    cleanup_ephemeral
    exit "$rc"
fi

hdr "⑧ Persist diffs (prompt + src + tests)"
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

artifact_diff \
    "$ARTIFACTS/src/foo_work_before.py" \
    "$ARTIFACTS/src/foo_work_after.py" \
    "src_before_vs_after.diff" \
    "src/foo_work_before.py (pre-clarify)" \
    "src/foo_work_after.py (post-clarify)" \
    "$REPORTS"
HUNKS_SRC="$(grep -c '^@@' "$DIFFS/src_before_vs_after.diff" 2>/dev/null || echo 0)"

artifact_diff \
    "$ARTIFACTS/tests/test_foo_work_before.py" \
    "$ARTIFACTS/tests/test_foo_work_after.py" \
    "tests_before_vs_after.diff" \
    "tests/test_foo_work_before.py (pre-clarify)" \
    "tests/test_foo_work_after.py (post-clarify)" \
    "$REPORTS"
HUNKS_TEST="$(grep -c '^@@' "$DIFFS/tests_before_vs_after.diff" 2>/dev/null || echo 0)"

write_live_json

hdr "⑨ Live summary"
echo "  prompt warnings:  ${WARN_BEFORE} → ${WARN_AFTER}"
echo "  ambiguities:      ${AMB_COUNT}"
echo "  compile errors:   ${COMPILE_ERR}"
echo "  src bytes:        ${GEN_BYTES_BEFORE} → ${GEN_BYTES_AFTER}"
echo "  test bytes:       ${TEST_BYTES_BEFORE} → ${TEST_BYTES_AFTER}"
echo "  py_compile:       $([[ "$SYNTAX_BEFORE" == "1" ]] && echo OK || echo FAIL) → $([[ "$SYNTAX_AFTER" == "1" ]] && echo OK || echo FAIL)"
echo "  pytest:           $([[ "$PYTEST_BEFORE" == "1" ]] && echo PASS || echo FAIL) → $([[ "$PYTEST_AFTER" == "1" ]] && echo PASS || echo FAIL)"
echo "  artifacts:        $ARTIFACTS/"
echo "  diffs:"
echo "    prompt: $DIFFS/prompt_codegen_before_vs_clarified.diff (${HUNKS_BC} hunk(s))"
echo "    src:    $DIFFS/src_before_vs_after.diff (${HUNKS_SRC} hunk(s))"
echo "    tests:  $DIFFS/tests_before_vs_after.diff (${HUNKS_TEST} hunk(s))"

FAIL=0
if [[ "$AMB_COUNT" -lt 1 ]]; then
    echo "  FAIL: expected >=1 ambiguity from clarify" >&2
    FAIL=1
fi
if [[ "$WARN_AFTER" -gt "$WARN_BEFORE" ]]; then
    echo "  FAIL: warnings increased after clarify" >&2
    FAIL=1
fi
if [[ "$GEN_BYTES_BEFORE" -le 0 || "$GEN_BYTES_AFTER" -le 0 ]]; then
    echo "  FAIL: generate produced empty output" >&2
    FAIL=1
fi
if [[ "$TEST_BYTES_BEFORE" -le 0 || "$TEST_BYTES_AFTER" -le 0 ]]; then
    echo "  FAIL: test generation produced empty output" >&2
    FAIL=1
fi
# Record pytest pass rate; require AFTER >= BEFORE (improvement or same).
if [[ "$PYTEST_AFTER" -lt "$PYTEST_BEFORE" ]]; then
    echo "  FAIL: pytest regressed (before=${PYTEST_BEFORE} after=${PYTEST_AFTER})" >&2
    FAIL=1
fi

cleanup_ephemeral

if [[ "$FAIL" -ne 0 ]]; then
    echo "  Live E2E FAILED" >&2
    exit 1
fi
echo "  Live E2E passed (before/after codegen stacks + clarify + artifact diffs)."
exit 0
