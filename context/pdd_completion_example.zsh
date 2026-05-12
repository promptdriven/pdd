#!/usr/bin/env zsh
# Example: load PDD zsh completion from a source checkout.

set -e

repo_root="${0:A:h:h}"
completion_file="$repo_root/pdd/pdd_completion.zsh"

if [[ ! -f "$completion_file" ]]; then
  print -u2 "Missing completion file: $completion_file"
  exit 1
fi

# Source the script from an interactive zsh session or from ~/.zshrc.
source "$completion_file"

# After loading, zsh should know the completion function for `pdd`.
whence -w _pdd >/dev/null
