#!/usr/bin/env bash
#
# Public-safe user-story regression lane.
#
# Runs the story-backed regression oracles (``pytest -m story``) with the same
# deterministic/offline guarantees as regression_public.sh: no LLM calls, cloud
# calls, private repositories, Infisical, GCP, or API credentials. Safe to run on
# public GitHub Actions for fork PRs without secrets.
#
# Story-marked tests are discovered automatically by the ``story`` marker, so
# adding a new story-backed test requires no manual registration here. The
# per-story pass/fail summary is emitted by the ``pytest_terminal_summary`` hook
# in tests/conftest.py.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

RUN_ROOT="${REGRESSION_TARGET_DIR:-$REPO_ROOT/staging/story_regression_$(date +%Y%m%d_%H%M%S)}"
SAFE_HOME="$RUN_ROOT/home"
LOG_FILE="$RUN_ROOT/story_regression.log"

mkdir -p "$SAFE_HOME/.config/gcloud"
touch "$LOG_FILE"

echo "[story-regression] repo: $REPO_ROOT" | tee -a "$LOG_FILE"
echo "[story-regression] log: $LOG_FILE" | tee -a "$LOG_FILE"

# Offline prelude: make accidental LLM/cloud paths fail fast instead of using
# developer credentials that happen to be present in the environment.
export HOME="$SAFE_HOME"
export XDG_CONFIG_HOME="$SAFE_HOME/.config"
export CLOUDSDK_CONFIG="$SAFE_HOME/.config/gcloud"
unset OPENAI_API_KEY
unset ANTHROPIC_API_KEY
unset GEMINI_API_KEY
unset GOOGLE_API_KEY
unset GOOGLE_APPLICATION_CREDENTIALS
unset VERTEXAI_PROJECT
unset VERTEXAI_LOCATION
unset AWS_ACCESS_KEY_ID
unset AWS_SECRET_ACCESS_KEY
unset AWS_SESSION_TOKEN
unset AWS_PROFILE
unset AZURE_API_KEY
unset AZURE_OPENAI_API_KEY
unset AZURE_OPENAI_ENDPOINT
unset FIREWORKS_API_KEY
unset GROQ_API_KEY
unset MISTRAL_API_KEY
unset TOGETHER_API_KEY
unset XAI_API_KEY
unset FIRECRAWL_API_KEY
unset PDD_JWT_TOKEN
unset GH_TOKEN
unset GITHUB_TOKEN
unset NEXT_PUBLIC_FIREBASE_API_KEY
unset GITHUB_CLIENT_ID
unset INFISICAL_TOKEN

export PDD_AUTO_UPDATE=false
export PDD_CLOUD_ONLY=false
export PDD_FORCE_LOCAL=true
export PDD_RUN_LLM_TESTS=0
export PDD_RUN_REAL_LLM_TESTS=0
export PDD_SUPPRESS_SETUP_REMINDER=1
export PDD_PATH="$REPO_ROOT/pdd"
export PYTHONPATH="$REPO_ROOT${PYTHONPATH:+:$PYTHONPATH}"

cd "$REPO_ROOT"

echo "[story-regression] Running: pytest -m story (deterministic/offline)" | tee -a "$LOG_FILE"

# Run single-process (no xdist) so the per-story summary in conftest.py
# aggregates across the whole session.
set +e
python -m pytest tests/ -m story --no-header -p no:cacheprovider "$@" 2>&1 | tee -a "$LOG_FILE"
status=${PIPESTATUS[0]}
set -e

# pytest exit code 5 == "no tests collected". Until story-backed tests are
# added (issue #1701 sub-issue 2), the lane has nothing to run; treat that as a
# green, no-op lane rather than a failure.
if [ "$status" -eq 5 ]; then
  echo "[story-regression] No story-marked tests collected yet; lane is green (nothing to run)." | tee -a "$LOG_FILE"
  exit 0
fi

if [ "$status" -ne 0 ]; then
  echo "[story-regression] ERROR: story regression lane failed (exit $status)" | tee -a "$LOG_FILE" >&2
  exit "$status"
fi

echo "[story-regression] Story regression lane completed successfully" | tee -a "$LOG_FILE"
