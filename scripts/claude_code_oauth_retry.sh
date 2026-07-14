#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -lt 2 ]; then
  echo "usage: $0 OUTPUT_FILE COMMAND [ARGS...]" >&2
  exit 2
fi

output_file="$1"
shift

stdin_file="$(mktemp)"
stdout_file="$(mktemp)"
stderr_file="$(mktemp)"
trap 'rm -f "$stdin_file" "$stdout_file" "$stderr_file"' EXIT
cat >"$stdin_file"

is_quota_or_auth_failure() {
  grep -Eiq \
    -e 'your organization has disabled claude subscription access for claude code' \
    -e "you('ve| have) hit your (weekly |usage |session )?limit.*reset" \
    -e '^[[:space:]]*(error(:|[[:space:]])[[:space:]]*)?(weekly (usage )?limit|usage limit|session limit|quota (exhausted|exceeded|reached))([:.[:space:]].*)?$' \
    -e '^[[:space:]]*(error(:|[[:space:]])[[:space:]]*)?(not logged in|please run /login|claude auth login|authentication failed|invalid (bearer|api key|key)|401([[:space:]]+unauthorized)?|unauthorized|access denied|permission denied)([:.[:space:]].*)?$'
}

run_attempt() {
  retryable_failure=false
  : >"$stdout_file"
  : >"$stderr_file"

  if "$@" <"$stdin_file" >"$stdout_file" 2>"$stderr_file"; then
    command_status=0
  else
    command_status=$?
  fi

  if cat "$stderr_file" "$stdout_file" 2>/dev/null | is_quota_or_auth_failure; then
    retryable_failure=true
    return 1
  fi
  if [ "$command_status" -ne 0 ]; then
    cat "$stderr_file" >&2
    return "$command_status"
  fi
  if [ ! -s "$stdout_file" ]; then
    echo "::error::Claude Code produced no output." >&2
    return 1
  fi

  cp "$stdout_file" "$output_file"
  return 0
}

token_names=(
  CLAUDE_CODE_OAUTH_TOKEN_1
  CLAUDE_CODE_OAUTH_TOKEN_2
  CLAUDE_CODE_OAUTH_TOKEN_3
  CLAUDE_CODE_OAUTH_TOKEN
)
token_values=(
  "${CLAUDE_CODE_OAUTH_TOKEN_1:-}"
  "${CLAUDE_CODE_OAUTH_TOKEN_2:-}"
  "${CLAUDE_CODE_OAUTH_TOKEN_3:-}"
  "${CLAUDE_CODE_OAUTH_TOKEN:-}"
)

attempted=0
for token_index in "${!token_names[@]}"; do
  token_name="${token_names[$token_index]}"
  token="${token_values[$token_index]}"
  if [ -z "$token" ]; then
    continue
  fi
  attempted=$((attempted + 1))
  export CLAUDE_CODE_OAUTH_TOKEN="$token"
  echo "Trying Claude Code OAuth token slot ${token_name}."
  if run_attempt "$@"; then
    exit 0
  else
    status=$?
  fi
  if [ "$retryable_failure" = true ]; then
    echo "::warning::Claude Code failed with quota/auth using ${token_name}; trying next token." >&2
    continue
  fi
  exit "$status"
done

if [ "$attempted" -eq 0 ]; then
  if run_attempt "$@"; then
    exit 0
  else
    status=$?
  fi
  if [ "$retryable_failure" = true ]; then
    echo "::error::Claude Code failed with a quota/auth diagnostic." >&2
  fi
  exit "$status"
fi

echo "::error::Claude Code failed with every configured OAuth token slot." >&2
exit 1
