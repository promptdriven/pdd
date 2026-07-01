#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -lt 2 ]; then
  echo "usage: $0 OUTPUT_FILE COMMAND [ARGS...]" >&2
  exit 2
fi

output_file="$1"
shift

stdin_file="$(mktemp)"
stderr_file="$(mktemp)"
trap 'rm -f "$stdin_file" "$stderr_file"' EXIT
cat >"$stdin_file"

is_quota_or_auth_failure() {
  grep -Eiq \
    'hit your .*limit.*reset|weekly .*limit|usage .*limit|session .*limit|quota (exhausted|exceeded|reached)|not logged in|please run /login|claude auth login|authentication failed|invalid (bearer|api key|key)|\b401\b|unauthorized|access denied|permission denied'
}

token_names=(
  CLAUDE_CODE_OAUTH_TOKEN_1
  CLAUDE_CODE_OAUTH_TOKEN_2
  CLAUDE_CODE_OAUTH_TOKEN_3
  CLAUDE_CODE_OAUTH_TOKEN
)

attempted=0
for token_name in "${token_names[@]}"; do
  token="${!token_name:-}"
  if [ -z "$token" ]; then
    continue
  fi
  attempted=$((attempted + 1))
  export CLAUDE_CODE_OAUTH_TOKEN="$token"
  echo "Trying Claude Code OAuth token slot ${token_name}."
  if "$@" <"$stdin_file" >"$output_file" 2>"$stderr_file"; then
    exit 0
  fi
  status=$?
  cat "$stderr_file" >&2
  if [ -s "$output_file" ]; then
    cat "$output_file" >&2
  fi
  if cat "$stderr_file" "$output_file" 2>/dev/null | is_quota_or_auth_failure; then
    echo "::warning::Claude Code failed with quota/auth using ${token_name}; trying next token." >&2
    continue
  fi
  exit "$status"
done

if [ "$attempted" -eq 0 ]; then
  "$@" <"$stdin_file" >"$output_file"
  exit $?
fi

echo "::error::Claude Code failed with every configured OAuth token slot." >&2
exit 1
