#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "Usage: $0 <agentic|pdd> <run_id>"
  exit 1
fi

ARM="$1"
RUN_ID="$2"

if [[ "$ARM" != "agentic" && "$ARM" != "pdd" ]]; then
  echo "Error: arm must be 'agentic' or 'pdd'."
  exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
BASELINE_DIR="${ROOT_DIR}/baseline"
RUN_DIR="${ROOT_DIR}/runs/${ARM}/run_${RUN_ID}"
WORKSPACE_DIR="${RUN_DIR}/workspace"

mkdir -p "${RUN_DIR}"
rm -rf "${WORKSPACE_DIR}"
mkdir -p "${WORKSPACE_DIR}"

cp -R "${BASELINE_DIR}/." "${WORKSPACE_DIR}/"
mkdir -p "${WORKSPACE_DIR}/examples"

cat > "${WORKSPACE_DIR}/.pddrc" <<'YAML'
version: "1.0"

contexts:
  default:
    defaults:
      generate_output_path: "src/"
      test_output_path: "tests/"
      example_output_path: "examples/"
      prompts_dir: "prompts/"
      default_language: "python"
      target_coverage: 80.0
      strength: 1.0
      temperature: 0.0
      budget: 20.0
      max_attempts: 3
YAML

cat > "${RUN_DIR}/run_meta.txt" <<EOF
arm=${ARM}
run_id=${RUN_ID}
created_utc=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
workspace=${WORKSPACE_DIR}
EOF

echo "Created workspace: ${WORKSPACE_DIR}"
