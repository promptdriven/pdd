"""
example_update_model_costs.py
─────────────────────────────
End-to-end demonstration of the `update_model_costs.py` helper that
lives inside the *pdd* package.

What you will learn
───────────────────
1. How to create (or point to) an `llm_model.csv` file.
2. How to invoke `pdd.update_model_costs.update_model_data` **directly
   from Python** or through its **command-line interface (CLI)**.
3. What the function expects and what it produces.

Prerequisites
─────────────
• The PDD package is already on the PYTHONPATH and can be imported with
  `from pdd.update_model_costs import update_model_data`.
• All required environment variables/API keys for LiteLLM are already
  configured in your shell (e.g. OPENAI_API_KEY, etc.).
• `pandas`, `rich`, and `litellm` are installed (they are if you can
  import `pdd.update_model_costs`).

CSV schema expected by the updater
──────────────────────────────────
provider,
model,
input (float, $ **per million** prompt tokens),
output (float, $ **per million** completion tokens),
coding_arena_elo,
base_url,
api_key,
counter,
encoder,
max_tokens,
max_completion_tokens,
max_reasoning_tokens,
structured_output (boolean: TRUE/FALSE)

In this example the *cost* and *structured_output* fields are left
blank so the script can fill them in.
"""

from pathlib import Path
import os
import pandas as pd

# 1. Create a minimal CSV -----------------------------------------------------------------

demo_csv_path = Path("sample_llm_model.csv")

demo_csv_path.write_text(
    """provider,model,input,output,coding_arena_elo,base_url,api_key,counter,encoder,max_tokens,max_completion_tokens,max_reasoning_tokens,structured_output
OpenAI,openai/gpt-4o-mini,,,1246,,,,tiktoken,,32768,,,
Anthropic,anthropic/claude-3-haiku-20240307,,,1300,,,,tiktoken,,200000,,,
"""
)

print(f"Created demo csv → {demo_csv_path.resolve()}\n")
print(pd.read_csv(demo_csv_path), "\n")  # show BEFORE state

# 2. Call the updater (library style) ------------------------------------------------------

from pdd.update_model_costs import update_model_data

update_model_data(str(demo_csv_path))   # the function edits the file *in place*

# 3. Inspect results ----------------------------------------------------------------------

print("\n=== AFTER running update_model_data ===")
print(pd.read_csv(demo_csv_path))

# 4. (Optional) Invoke via CLI exactly the same way ---------------------------------------
#    Uncomment the three lines below to see the argparse interface in action.
#    NOTE: because we pass --csv-path explicitly no user input is required.

# import subprocess, sys
# subprocess.run(
#     [sys.executable, "-m", "pdd.update_model_costs", "--csv-path", str(demo_csv_path)],
#     check=True,
# )