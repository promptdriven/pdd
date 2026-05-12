# Example: load PDD fish completion from a source checkout.

set repo_root (dirname (dirname (status --current-filename)))
set completion_file "$repo_root/pdd/pdd_completion.fish"

if not test -f "$completion_file"
    echo "Missing completion file: $completion_file" >&2
    exit 1
end

# Source this from an interactive fish session or copy it to:
# ~/.config/fish/completions/pdd.fish
source "$completion_file"

# After loading, fish should list completions for the `pdd` command.
complete --command pdd >/dev/null

