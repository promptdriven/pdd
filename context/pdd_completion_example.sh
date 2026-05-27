#!/usr/bin/env bash
# Example: load PDD bash completion from a source checkout.

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
completion_file="$repo_root/pdd/pdd_completion.sh"

if [[ ! -f "$completion_file" ]]; then
  echo "Missing completion file: $completion_file" >&2
  exit 1
fi

# Source the script in an interactive bash session or from ~/.bashrc.
# shellcheck source=/dev/null
source "$completion_file"

# After loading, bash should know the completion function for `pdd`.
complete -p pdd >/dev/null
