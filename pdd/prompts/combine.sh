#!/bin/bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
output_file="$script_dir/combined_output.txt"

> "$output_file"

for file in "$script_dir"/*.prompt; do
  if [[ -f "$file" ]]; then
    echo "===== $(basename "$file") =====" >> "$output_file"
    sed 's/[[:space:]]*$//' "$file" >> "$output_file"
    printf '\n\n' >> "$output_file"
  fi
done

echo "All files have been combined into $output_file"
