# Getting Started with PDD using a Free Gemini API Key

This example shows you how to set up **Prompt-Driven Development (PDD)** with a free **Gemini API key** and run the built-in **Hello** example.

> **Goal:** By the end, you'll have PDD installed, Gemini configured, and `pdd sync` running on the Hello example.

---

## 1. Install the `pdd` CLI

PDD works best in an isolated environment. You can pick one of these methods:

### Option A — uv (recommended)

**macOS/Linux**
```bash
curl -LsSf https://astral.sh/uv/install.sh | sh
uv tool install pdd-cli
pdd --version
```

**Windows (PowerShell)**
```powershell
irm https://astral.sh/uv/install.ps1 | iex
uv tool install pdd-cli
pdd --version
```

---

### Option B — pipx
```bash
python -m pip install --user pipx
python -m pipx ensurepath
pipx install pdd-cli
pdd --version
```

---

### Option C — venv
```bash
python -m venv ~/.venvs/pdd
source ~/.venvs/pdd/bin/activate   # Windows: %USERPROFILE%\venvs\pdd\Scripts\activate
pip install --upgrade pip
pip install pdd-cli
pdd --version
```

✅ If you see `pdd, version X.Y.Z`, installation worked.  
⚠️ If `pdd` isn’t found, try `~/.local/bin/pdd --version` once, then add `~/.local/bin` to your PATH.

---

## 2. Run the guided setup

Right after installation, let PDD bootstrap its configuration:

```bash
pdd setup
```

The setup wizard runs these steps:
  1.  Detects agentic CLI tools (Claude, Gemini, Codex) and offers installation and API key configuration if needed
  2. Scans for API keys across `.env`, and `~/.pdd/api-env.*`, and the shell environment; prompts to add one if none are found
  3. Configures models from a reference CSV `data/llm_model.csv` of top models (ELO ≥ 1400) across all LiteLLM-supported providers  based on your available keys
  4. Optionally creates a `.pddrc` project config
  5. Tests the first available model with a real LLM call 
  6. Prints a structured summary (CLIs, keys, models, test result)

When adding your Gemini API key:
- Select Gemini CLI as one of the agentic CLI tools
- The wizard will detect that `GEMINI_API_KEY` is missing
- Paste your API key when prompted (you can create it in the next step if you haven't already)
- The wizard tests it immediately and confirms it works

The wizard writes your credentials to `~/.pdd/api-env.zsh` (or `.bash`) and updates `llm_model.csv` with your selected models.

> **Important:** After setup completes, source the API environment file so your keys take effect in the current terminal session:
> ```bash
> source ~/.pdd/api-env.zsh   # or api-env.bash, depending on your shell
> ```
> New terminal windows will load keys automatically.

If you prefer to configure everything manually—or you're on an offline machine—skip the wizard and follow the manual instructions below.

---

## 3. Clone the repo

```bash
git clone https://github.com/promptdriven/pdd.git
cd pdd/examples/hello
```

## 4. Configure your Google API Key (manual setup)

If you already pasted the key into `pdd setup`, you can skip this section. Otherwise:

1. Go to [Google AI Studio](https://aistudio.google.com/app/apikey).
2. Log in with your Google account.
3. Click **Create API key**.
4. Copy the key.

> **Students:** The Gemini API is free for everyone, but university students get higher rate limits (60 requests/min, 300K tokens/day) extended through June 2026. You can also claim [1 year of Google AI Pro free](https://gemini.google/students/) (sign up by Jan 31, 2026) for additional perks like NotebookLM and 2TB storage.

**macOS/Linux (bash/zsh)**
```bash
export GEMINI_API_KEY="PASTE_YOUR_KEY_HERE"
```

**Windows (PowerShell)**
```powershell
setx GEMINI_API_KEY "PASTE_YOUR_KEY_HERE"
```

Then close and reopen your terminal.  
Check:
```bash
echo $GEMINI_API_KEY     # macOS/Linux
echo $Env:GEMINI_API_KEY # Windows
```

---

## 5. Create `~/.pdd/llm_model.csv` (manual setup)

The setup wizard already adds a Gemini row. Only follow this step if you skipped the wizard or want to edit the file by hand. Add Gemini rows so PDD knows how to call the Google AI Studio models:

```csv
provider,model,input,output,coding_arena_elo,base_url,api_key,max_reasoning_tokens,structured_output,reasoning_type
gemini,gemini/gemini-2.5-pro,0,0,0,,GEMINI_API_KEY,0,True,none
```

Make sure the file exists:
```bash
head -2 ~/.pdd/llm_model.csv
```

---

## 6. Output locations (optional, skip for this quickstart)

By default, PDD writes generated files next to your source code. For real projects, you can set these environment variables to organize outputs:

```bash
export PDD_TEST_OUTPUT_PATH=tests
export PDD_EXAMPLE_OUTPUT_PATH=examples
```

With these set, PDD will place outputs like so:
- Examples → `examples/<module>/...`
- Tests → `tests/<module>/...`

> **Note:** For the Hello example below, leave these unset so files generate in the current directory.

---

## 7. Validate Your Setup

Before using the main workflow, verify your configuration works by running a quick generate:

From `pdd/examples/hello`:

```bash
pdd generate hello_python.prompt
```

If this succeeds, your API key and model configuration are working correctly.

---

## 8. Use Sync (Primary Workflow)

The `pdd sync` command is the primary way to work with PDD. It generates code, tests, and examples for a module, keeping everything in sync:

```bash
pdd sync hello
```

Use `--force` to regenerate even if files already exist:

```bash
pdd --force sync hello
```

After syncing, run the generated example:

```bash
python hello.py
```

If the generated `hello.py` is minimal (no `__main__` block), run it interactively:

```bash
python -i hello.py
>>> hello()
hello
```

---

## 9. What if nothing prints?

Sometimes the generated file only defines the function (e.g., `def hello(): print("hello")`) but doesn’t include the standard Python entry point:

```python
if __name__ == "__main__":
    hello()
```

In that case you have two options:

### Option A — Run interactively
```bash
python -i hello.py
>>> hello()
hello
```

### Option B — Add a main guard
Append this to the bottom of the file:
```python
if __name__ == "__main__":
    hello()
```
Then re-run:
```bash
python hello.py
# output:
hello
```


---

## 10. Try the Web Interface with `pdd connect`

PDD also provides a web-based interface for generating code and managing projects. Start the local server:

```bash
pdd connect
```

This launches a FastAPI server on `http://localhost:9876` and opens your browser automatically.

From the web interface you can:
- Generate code from prompts visually
- Implement GitHub issues automatically
- Manage PDD projects through a GUI

Common options:

```bash
# Use a different port
pdd connect --port 8000

# Don't auto-open the browser
pdd connect --no-browser

# View API docs at http://localhost:9876/docs
```

Press `Ctrl+C` to stop the server when you're done.

---

✅ That's it! You've installed PDD, configured Gemini, and used `pdd sync` to generate your first module.
