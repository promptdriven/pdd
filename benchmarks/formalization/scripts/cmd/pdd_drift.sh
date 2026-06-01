#!/usr/bin/env bash
# Exactly one command: pdd checkup drift <devunit> --from-evidence <json> --code-file <py> [--dry-run] --json
#   TASK=email_validator ARM=A0 MODE=dry-run bash .../pdd_drift.sh
set -euo pipefail
# shellcheck source=_env.sh
source "$(dirname "$0")/_env.sh"
MODE="${MODE:-dry-run}"
_resolve m3
[[ -f "${CODE}" ]] || { echo "Missing M2 code: ${CODE}" >&2; exit 1; }

# Write minimal evidence if missing (drift requires --from-evidence)
if [[ ! -f "${EVIDENCE}" ]]; then
  mkdir -p "$(dirname "${EVIDENCE}")"
  python - <<PY
import hashlib, json
from pathlib import Path
prompt = Path("${PROMPT}")
code = Path("${CODE}")
root = Path("${REPO_ROOT}")
def rel(p):
    try: return str(p.resolve().relative_to(root))
    except ValueError: return str(p.resolve())
payload = {
    "schema_version": 1,
    "prompt": {"path": rel(prompt)},
    "outputs": [{"path": rel(code), "sha256": hashlib.sha256(code.read_bytes()).hexdigest()}],
}
Path("${EVIDENCE}").write_text(json.dumps(payload, indent=2) + "\\n")
PY
fi

CMD=(pdd checkup drift "${DEVUNIT}" --from-evidence "${EVIDENCE}" --code-file "${CODE}" --json)
if [[ "${MODE}" == "dry-run" ]]; then
  CMD+=(--dry-run)
fi
_run_cmd "${CMD[@]}"
