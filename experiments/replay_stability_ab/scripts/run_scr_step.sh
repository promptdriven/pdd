#!/usr/bin/env bash
set -euo pipefail

# Run a single SCR step for a given arm.
# Usage: ./scripts/run_scr_step.sh <arm> <run_id> <step>

if [[ $# -ne 3 ]]; then
  echo "Usage: $0 <agentic|pdd> <run_id> <step>"
  exit 1
fi

ARM="$1"
RUN_ID="$2"
STEP="$3"

if [[ "$ARM" != "agentic" && "$ARM" != "pdd" ]]; then
  echo "Error: arm must be 'agentic' or 'pdd'."
  exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
RUN_DIR="${ROOT_DIR}/runs/${ARM}/run_${RUN_ID}"
WORKSPACE="${RUN_DIR}/workspace"
STEPS_DIR="${ROOT_DIR}/steps"
META_FILE="${RUN_DIR}/step_${STEP}_meta.txt"

if [[ ! -d "$WORKSPACE" ]]; then
  echo "Error: workspace not found: ${WORKSPACE}"
  exit 1
fi

# Copy ONLY the current step's test file into the workspace
mkdir -p "${WORKSPACE}/tests"
cp "${STEPS_DIR}/test_acceptance_step_${STEP}.py" "${WORKSPACE}/tests/test_acceptance_step_${STEP}.py"

echo "--- SCR Step ${STEP} | arm=${ARM} | run=${RUN_ID} ---"

if [[ "$ARM" == "agentic" ]]; then
  # Copy change request into workspace for Claude to read
  cp "${STEPS_DIR}/step_${STEP}_change.md" "${WORKSPACE}/CHANGE_REQUEST.md"

  CHANGE_CONTENT="$(cat "${STEPS_DIR}/step_${STEP}_change.md")"

  MAX_ATTEMPTS=3
  ATTEMPT=1
  PASSED=false
  LAST_FAILURE=""

  while [[ $ATTEMPT -le $MAX_ATTEMPTS ]]; do
    echo "=== Agentic attempt ${ATTEMPT}/${MAX_ATTEMPTS} for step ${STEP} ==="

    OUTPUT_FILE="${RUN_DIR}/claude_step_${STEP}_attempt_${ATTEMPT}.json"

    if [[ $ATTEMPT -eq 1 ]]; then
      PROMPT="${CHANGE_CONTENT}"
    else
      PROMPT="The previous attempt failed. Here is the test output:

${LAST_FAILURE}

Please fix the code in src/user_id_parser.py to pass all tests in tests/test_acceptance_step_${STEP}.py.

Original change request:

${CHANGE_CONTENT}"
    fi

    # Run Claude Code in print mode
    cd "${WORKSPACE}"
    claude -p \
      --dangerously-skip-permissions \
      --model claude-opus-4-6 \
      --max-turns 25 \
      --output-format json \
      "${PROMPT}" > "${OUTPUT_FILE}" 2>&1 || true

    # Check if tests pass
    TEST_OUTPUT="$(cd "${WORKSPACE}" && pytest -q "tests/test_acceptance_step_${STEP}.py" 2>&1)" || true

    if echo "$TEST_OUTPUT" | grep -q " passed" && ! echo "$TEST_OUTPUT" | grep -qE "failed|error"; then
      PASSED=true
      echo "Tests PASSED on attempt ${ATTEMPT}."
      break
    else
      LAST_FAILURE="$TEST_OUTPUT"
      echo "Tests FAILED on attempt ${ATTEMPT}."
    fi

    ATTEMPT=$((ATTEMPT + 1))
  done

  # Write step metadata
  cat > "$META_FILE" <<EOF
arm=${ARM}
run_id=${RUN_ID}
step=${STEP}
passed=${PASSED}
attempts=${ATTEMPT}
EOF

  echo "Step ${STEP} result: passed=${PASSED}, attempts=${ATTEMPT}"

elif [[ "$ARM" == "pdd" ]]; then
  # Copy the cumulative prompt into the workspace prompt file
  mkdir -p "${WORKSPACE}/prompts"
  cp "${STEPS_DIR}/prompt_step_${STEP}.txt" "${WORKSPACE}/prompts/user_id_parser_python.prompt"

  # Run PDD sync
  cd "${WORKSPACE}"
  pdd --force --local sync user_id_parser 2>&1 | tee "${RUN_DIR}/pdd_step_${STEP}.log" || true

  # Check if tests pass
  TEST_OUTPUT="$(cd "${WORKSPACE}" && pytest -q "tests/test_acceptance_step_${STEP}.py" 2>&1)" || true

  if echo "$TEST_OUTPUT" | grep -q " passed" && ! echo "$TEST_OUTPUT" | grep -qE "failed|error"; then
    PASSED=true
  else
    PASSED=false
  fi

  # Write step metadata
  cat > "$META_FILE" <<EOF
arm=${ARM}
run_id=${RUN_ID}
step=${STEP}
passed=${PASSED}
attempts=1
EOF

  echo "Step ${STEP} result: passed=${PASSED}"
fi
