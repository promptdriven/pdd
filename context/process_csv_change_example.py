# run_demo.py
# ---------------------------------------------------
# Concise usage example for pdd.process_csv_change.process_csv_change
# ---------------------------------------------------
from pathlib import Path
from pprint import pprint

# 1) Import the function
from pdd.process_csv_change import process_csv_change

# ---------------------------------------------------
# 2)  Set-up: create a tiny workspace on disk
# ---------------------------------------------------
workspace        = Path("output/example_workspace")   # root for demo assets
code_dir         = workspace / "code"                 # <-- will be passed as `code_directory`
code_dir.mkdir(parents=True, exist_ok=True)

# ----  a)  Source code file  ------------------------
(code_dir / "factorial.py").write_text(
    "def factorial(n):\n"
    "    '''Return n!'''\n"
    "    return 1 if n in (0, 1) else n * factorial(n-1)\n",
    encoding="utf-8"
)

# ----  b)  Prompt file (must follow *_<language>.prompt naming) ----
prompt_path = code_dir / "factorial_python.prompt"
prompt_path.write_text(
    "Write a test for the factorial function.",
    encoding="utf-8"
)

# ----  c)  CSV file with instructions ----------------
csv_path = workspace / "tasks.csv"
csv_path.write_text(
    "prompt_name,change_instructions\n"
    f"{prompt_path},Add an example section to the prompt.\n",
    encoding="utf-8"
)

# ---------------------------------------------------
# 3)  Call process_csv_change
# ---------------------------------------------------
success, list_of_jsons, total_cost, model_name = process_csv_change(
    csv_file      = str(csv_path),  # path to the CSV created above
    strength      = 0.5,            # 0.0-1.0 — how "strongly" to apply the edit
    temperature   = 0.0,            # 0.0-1.0 — sampling temperature for the LLM
    code_directory= str(code_dir),  # directory housing .py and .prompt
    language      = "python",       # only used for naming convention
    extension     = ".py",          # file extension of the source code
    budget        = 0.25            # USD budget (or whatever units your change() uses)
)

# ---------------------------------------------------
# 4)  Inspect the returned data programmatically
# ---------------------------------------------------
print("\n=== Returned values ==================================")
print("success      :", success)
print("total_cost   :", total_cost)
print("model_name   :", model_name)
print("list_of_jsons:")
pprint(list_of_jsons, compact=True)

# === Returned values ==================================
# success      : True
# total_cost   : 0.0054053
# model_name   : gpt-5-nano
# list_of_jsons:
# [{'file_name': 'factorial_python.prompt',
#   'modified_prompt': 'Write a test for the factorial function.\n'
#                      '\n'
#                      'Here is an example of how to write such a test:\n'
#                      '```python\n'
#                      'def test_factorial():\n'
#                      '    assert factorial(5) == 120\n'
#                      '    assert factorial(0) == 1\n'
#                      '    assert factorial(3) == 6\n'
#                      '```'}]