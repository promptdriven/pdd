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
publish_file=""
# Invoked indirectly by the EXIT trap below.
# shellcheck disable=SC2329
cleanup() {
  rm -f "$stdin_file" "$stdout_file" "$stderr_file"
  if [ -n "$publish_file" ]; then
    rm -f "$publish_file"
  fi
}
trap cleanup EXIT
cat >"$stdin_file"

is_quota_or_auth_failure() {
  grep -Eiq \
    -e 'your organization has disabled claude subscription access for claude code' \
    -e "you('ve| have) hit your (weekly |usage |session )?limit.*reset" \
    -e '^[[:space:]]*(error:[[:space:]]*)?quota (exhausted|exceeded|reached)[.!]?[[:space:]]*$' \
    -e '^[[:space:]]*(error:[[:space:]]*)?(weekly (usage )?limit|usage limit|session limit)[[:space:]]+(has been[[:space:]]+)?(reached|exceeded)([.![:space:]].*)?$' \
    -e '^[[:space:]]*(api error:[[:space:]]*)?401[[:space:]:-]+(invalid[[:space:]]+(api key|x-api-key|bearer token)|unauthorized)([.![:space:]].*)?$' \
    -e '^[[:space:]]*failed to authenticate\.[[:space:]]*api error:[[:space:]]*401[[:space:]:-]+invalid[[:space:]]+(api key|x-api-key|bearer token)([.![:space:]].*)?$' \
    -e '^[[:space:]]*\{.*"type"[[:space:]]*:[[:space:]]*"authentication_error".*\}[[:space:]]*$' \
    -e '^[[:space:]]*(error:[[:space:]]*)?authentication failed:[[:space:]]*(invalid|expired|missing|revoked)[[:space:]]+(api key|bearer token|token|key|credential)s?([.![:space:]].*)?$' \
    -e '^[[:space:]]*(error:[[:space:]]*)?invalid[[:space:]]+(api key|x-api-key|bearer token)[.!]?[[:space:]]*$' \
    -e '^[[:space:]]*(error:[[:space:]]*)?(not logged in|please run /login|claude auth login|unauthorized|access denied|permission denied)[.!]?[[:space:]]*$' \
    "$@"
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

  if is_quota_or_auth_failure "$stderr_file" "$stdout_file"; then
    retryable_failure=true
    return 1
  fi
  if [ "$command_status" -ne 0 ]; then
    echo "::error::Claude Code command failed with exit status ${command_status}." >&2
    return "$command_status"
  fi
  if [ ! -s "$stdout_file" ]; then
    echo "::error::Claude Code produced no output." >&2
    return 1
  fi

  case "$output_file" in
    */*)
      output_dir="${output_file%/*}"
      output_name="${output_file##*/}"
      ;;
    *)
      output_dir="."
      output_name="$output_file"
      ;;
  esac
  if ! publish_file=$(mktemp "${output_dir}/.${output_name}.XXXXXX" 2>/dev/null); then
    echo "::error::Unable to stage validated Claude Code output." >&2
    publish_file=""
    return 1
  fi
  if ! cp "$stdout_file" "$publish_file"; then
    echo "::error::Unable to stage validated Claude Code output." >&2
    rm -f "$publish_file"
    publish_file=""
    return 1
  fi
  if ! mv -f "$publish_file" "$output_file"; then
    echo "::error::Unable to publish validated Claude Code output." >&2
    rm -f "$publish_file"
    publish_file=""
    return 1
  fi
  publish_file=""
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
