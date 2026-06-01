#!/usr/bin/env bash
# Exactly one command: pdd checkup contract check <prompt> [--stories <dir>] --json
set -euo pipefail
# shellcheck source=_env.sh
source "$(dirname "$0")/_env.sh"
PROMPT_ARM="${PROMPT_ARM:-A0}"
if [[ "${PROMPT_ARM}" == "A1" ]]; then
  ARM=A1
  _resolve m2
  TARGET="${PROMPT}"
else
  _resolve m1
  TARGET="${A0_PROMPT}"
fi
STORIES=()
if [[ -n "${STORIES_DIR:-}" ]]; then
  STORIES=(--stories "${STORIES_DIR}")
fi
CMD=(pdd checkup contract check "${TARGET}" "${STORIES[@]}" --json)
_run_cmd "${CMD[@]}"
