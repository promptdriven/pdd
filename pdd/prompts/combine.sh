#!/bin/bash

# Output file where all contents will be combined
output_file="combined_output.txt"

# Empty the output file if it already exists
> "$output_file"

# Loop through all files in the current directory
for file in *.prompt; do
  # Check if it's a regular file (not a directory)
  if [[ -f "$file" ]]; then
    # Write the file name as a header
    echo "===== $file =====" >> "$output_file"
    # Append the file contents
    cat "$file" >> "$output_file"
    # Add a new line after the file contents
    echo -e "\n" >> "$output_file"
  fi
done

echo "All files have been combined into $output_file"