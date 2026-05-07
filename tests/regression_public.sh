#!/usr/bin/env bash
#
# Public-safe CLI regression tests.
#
# This suite is intentionally deterministic: no LLM calls, cloud calls, private
# repositories, Infisical, GCP, or API credentials. It covers command wiring and
# validation behavior that can run on public GitHub Actions for fork PRs.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

RUN_ROOT="${REGRESSION_TARGET_DIR:-$REPO_ROOT/staging/public_regression_$(date +%Y%m%d_%H%M%S)}"
WORK_DIR="$RUN_ROOT/work"
SAFE_HOME="$RUN_ROOT/home"
LOG_FILE="$RUN_ROOT/public_regression.log"

mkdir -p "$WORK_DIR"
mkdir -p "$SAFE_HOME/.config/gcloud"
touch "$LOG_FILE"

exec > >(tee -a "$LOG_FILE") 2>&1

echo "[public-regression] repo: $REPO_ROOT"
echo "[public-regression] work dir: $WORK_DIR"
echo "[public-regression] log: $LOG_FILE"

# Make accidental LLM/cloud paths fail fast instead of using local developer
# credentials that happen to be present in the environment.
export HOME="$SAFE_HOME"
export XDG_CONFIG_HOME="$SAFE_HOME/.config"
export CLOUDSDK_CONFIG="$SAFE_HOME/.config/gcloud"
unset OPENAI_API_KEY
unset ANTHROPIC_API_KEY
unset GEMINI_API_KEY
unset GOOGLE_API_KEY
unset VERTEXAI_PROJECT
unset VERTEXAI_LOCATION
unset PDD_JWT_TOKEN
unset NEXT_PUBLIC_FIREBASE_API_KEY
unset GITHUB_CLIENT_ID
unset INFISICAL_TOKEN

export PDD_AUTO_UPDATE=false
export PDD_CLOUD_ONLY=false
export PDD_FORCE_LOCAL=false
export PDD_QUIET=1
export PDD_RUN_LLM_TESTS=0
export PDD_RUN_REAL_LLM_TESTS=0
export PDD_SUPPRESS_SETUP_REMINDER=1
export PDD_PATH="$REPO_ROOT/pdd"
export PYTHONPATH="$REPO_ROOT${PYTHONPATH:+:$PYTHONPATH}"

if [ -x "$REPO_ROOT/pdd-local.sh" ]; then
  PDD_BASE_CMD=("$REPO_ROOT/pdd-local.sh")
else
  PDD_BASE_CMD=(python -c "from pdd.cli import cli; cli()")
fi
PDD_CMD=("${PDD_BASE_CMD[@]}" --quiet --no-core-dump --keep-core-dumps 0)

log() {
  echo ""
  echo "[public-regression] $*"
}

fail() {
  echo "[public-regression] ERROR: $*" >&2
  exit 1
}

run_pdd() {
  log "pdd $*"
  "${PDD_CMD[@]}" "$@"
}

expect_fail() {
  local output
  local status

  set +e
  output="$("$@" 2>&1)"
  status=$?
  set -e

  printf "%s\n" "$output"
  if [ "$status" -eq 0 ]; then
    fail "expected command to fail: $*"
  fi
}

check_file_contains() {
  local file="$1"
  local needle="$2"
  local description="$3"

  if ! grep -q "$needle" "$file"; then
    fail "$description missing '$needle' in $file"
  fi
}

check_file_not_contains() {
  local file="$1"
  local needle="$2"
  local description="$3"

  if grep -q "$needle" "$file"; then
    fail "$description unexpectedly found '$needle' in $file"
  fi
}

log "1. Architecture include validation"
run_pdd checkup --validate-arch-includes --project-root "$REPO_ROOT/tests/fixtures/arch_include_validate_ok"
run_pdd checkup --validate-arch-includes --project-root "$REPO_ROOT"

cd "$WORK_DIR"

cat > .pddrc <<'EOF'
contexts:
  default:
    defaults:
      default_language: "python"
  alt:
    defaults:
      default_language: "python"
  envonly:
    defaults:
      default_language: "python"
EOF

log "2. CLI globals and context validation"
run_pdd --help > cli_help.txt
check_file_contains cli_help.txt "Usage:" "CLI help"

run_pdd --list-contexts > contexts.txt
check_file_contains contexts.txt "^default$" "context listing"
check_file_contains contexts.txt "^alt$" "context listing"

cat > basic_python.prompt <<'EOF'
Plain prompt content for deterministic preprocessing.
EOF

expect_fail "${PDD_CMD[@]}" --context missing preprocess --output missing_context.prompt basic_python.prompt
run_pdd --context alt preprocess --output alt_preprocessed.prompt basic_python.prompt
[ -s alt_preprocessed.prompt ] || fail "preprocess with --context alt did not create output"

log "3. Deterministic preprocess behavior"
cat > include_me.txt <<'EOF'
Included deterministic content.
EOF

cat > complex_python.prompt <<'EOF'
Before include.
<include>include_me.txt</include>

<pdd>This internal comment should be stripped.</pdd>

Shell output:
<shell>printf "shell-output"</shell>

Curly braces:
Single: {value}
Double: {{value}}
EOF

run_pdd preprocess --output complex_preprocessed.prompt complex_python.prompt
check_file_contains complex_preprocessed.prompt "Included deterministic content." "preprocess include"
check_file_contains complex_preprocessed.prompt "shell-output" "preprocess shell"
check_file_not_contains complex_preprocessed.prompt "This internal comment should be stripped." "preprocess pdd comment stripping"

log "4. Trace validation without model calls"
cp "$REPO_ROOT/tests/fixtures/simple_math.py" simple_math.py
run_pdd trace --output invalid_trace.log "$REPO_ROOT/tests/fixtures/simple_math_python.prompt" simple_math.py 99999
check_file_contains invalid_trace.log "Prompt Line:" "trace fallback output"

log "5. Template registry and early validation"
run_pdd templates list > templates_list.txt
check_file_contains templates_list.txt "architecture/architecture_json" "templates list"

python - <<'PY'
from pathlib import Path
from pdd import template_registry

data = template_registry.show_template("architecture/architecture_json")
variables = data.get("variables") or {}
if "PRD_FILE" not in variables:
    raise SystemExit("PRD_FILE missing from architecture template metadata")
if not data.get("output_schema"):
    raise SystemExit("output_schema missing from architecture template metadata")

dest_dir = Path("copied_templates")
dest_dir.mkdir(parents=True, exist_ok=True)
dest = Path(template_registry.copy_template("architecture/architecture_json", str(dest_dir)))
if not dest.is_file():
    raise SystemExit(f"copied template not found: {dest}")
PY

cat > specs.md <<'EOF'
# Public CI Fixture
Build a small order tracker.
EOF

cat > tech_stack.md <<'EOF'
Backend: Python
EOF

set +e
"${PDD_CMD[@]}" generate --template architecture/architecture_json \
  -e TECH_STACK_FILE=tech_stack.md \
  -e DOC_FILES=specs.md \
  -e INCLUDE_FILES="" \
  --output missing_template.json > missing_template_error.txt 2>&1
set -e

check_file_contains missing_template_error.txt "Missing required variables" "template missing-variable validation"
check_file_contains missing_template_error.txt "PRD_FILE" "template missing-variable validation"
[ ! -e missing_template.json ] || fail "generate --template created output despite missing required variables"

log "6. Error handling that exits before model invocation"
expect_fail "${PDD_CMD[@]}" generate --output nonexistent.py nonexistent/prompt.prompt
expect_fail "${PDD_CMD[@]}" fix --output-test err_test.py --output-code err_code.py \
  "$REPO_ROOT/tests/fixtures/simple_math_python.prompt" simple_math.py nonexistent_test.py nonexistent_error.log

log "Public-safe CLI regression tests completed successfully"
