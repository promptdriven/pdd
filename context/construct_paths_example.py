"""
demo_construct_paths.py
~~~~~~~~~~~~~~~~~~~~~~~
Tiny end‑to‑end demo for pdd.construct_paths.construct_paths.

What it shows
-------------
1. Creates a toy prompt file in the current directory.
2. Calls `construct_paths` with the arguments normally supplied by the CLI.
3. Prints the three return values:
      • input_strings      –  the file contents that were just read
      • output_file_paths  –  where PDD will write its results
      • language           –  language detected for the operation
4. Removes the temporary file afterwards so the directory is left clean.

Run it:
    python demo_construct_paths.py
"""

import os
from pathlib import Path

from pdd.construct_paths import construct_paths

# ---------------------------------------------------------------------------
# 1. Prepare a minimal prompt file so the function has something to read
# ---------------------------------------------------------------------------
prompt_path = Path("Makefile_makefile.prompt").resolve()
prompt_path.write_text(
    "Prompt‑Driven Development example\n\n"
    "Task: Write a function `hello()` that returns the string 'Hello, world!'",
    encoding="utf-8",
)

# ---------------------------------------------------------------------------
# 2. Build the arguments expected by `construct_paths`
# ---------------------------------------------------------------------------
# The CLI layer normally supplies these.  We mimic that here.
input_file_paths = {
    "prompt_file": str(prompt_path),  # key name depends on the command
    # Optional: you could also add an 'error_file': "errors.log", etc.
}

force = True          # overwrite outputs if they already exist
quiet = False         # print nice Rich tables to the terminal
command = "generate"  # the PDD command we are emulating
command_options = {}  # '--output', '--language', … would land here

# ---------------------------------------------------------------------------
# 3. Invoke the helper – exactly what the CLI does internally
# ---------------------------------------------------------------------------
resolved_config, input_strings, output_file_paths, language = construct_paths(
    input_file_paths=input_file_paths,
    force=force,
    quiet=quiet,
    command=command,
    command_options=command_options,
)

# ---------------------------------------------------------------------------
# 4. Show the returned structures so you see what to expect
# ---------------------------------------------------------------------------
print("\nReturned values --------------------------------------------------")
print("input_strings:")
for key, value in input_strings.items():
    print(f"  {key}:")
    # Format multiline strings with proper indentation for better readability
    value_lines = value.split('\n')
    for line in value_lines:
        print(f"    {line}")

print("\noutput_file_paths:")
for key, value in output_file_paths.items():
    print(f"  {key}: {value}")

print(f"\nlanguage: {language}")

# ---------------------------------------------------------------------------
# 5. (Optional) Clean‑up – remove the temporary prompt so it doesn't litter
# ---------------------------------------------------------------------------
prompt_path.unlink(missing_ok=True)
