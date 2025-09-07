# Getting Started with PDD using a Free Gemini API Key

This example shows you how to set up **Prompt-Driven Development (PDD)** with a free Google **Google API key** and run the built-in **Hello** example.

> **Goal:** By the end, you’ll have PDD installed, Gemini configured, and `pdd generate` running on the Hello example.

---

## 1. Install the `pdd` CLI

PDD works best in an isolated environment. You can pick one of these methods:

### Option A — uv (recommended)

**macOS/Linux**
```bash
curl -LsSf https://astral.sh/uv/install.sh | sh
~/.local/bin/uv tool install pdd-cli
~/.local/bin/pdd --version
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

## 2) Clone the repo

```bash
git clone https://github.com/promptdriven/pdd.git
cd pdd/examples/hello
```

## 3. Configure your Google API Key

1. Go to [Google AI Studio](https://aistudio.google.com/app/apikey).  
2. Log in with your Google account.  
3. Click **Create API key**.  
4. Copy the key.

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

## 4. Create `~/.pdd/llm_model.csv`

Add Gemini rows so PDD knows how to call the Google AI Studio models:

```csv
provider,model,input,output,coding_arena_elo,base_url,api_key,max_reasoning_tokens,structured_output,reasoning_type
gemini,gemini/gemini-2.5-pro,0,0,0,,GEMINI_API_KEY,0,True,none
```

Make sure the file exists:
```bash
head -2 ~/.pdd/llm_model.csv
```

---

## 5. Output locations (tests & examples)

By default, PDD writes generated files next to your source code.  
To keep repos tidy, set these environment variables once (e.g., in `~/.zshrc` or `~/.bashrc`):

```bash
export PDD_TEST_OUTPUT_PATH=tests
export PDD_EXAMPLE_OUTPUT_PATH=examples
```

With these set, PDD will place outputs like so:
- Examples → `examples/<module>/...`
- Tests → `tests/<module>/...`

---

## 6. Run the Hello Example

From `pdd/examples/hello`:

```bash
# generate code from the prompt
pdd generate hello_python.prompt

# run the generated example if it has a main block
python examples/hello/hello.py
```

If the generated `hello.py` is minimal (no `__main__` block), run it interactively:

```bash
python -i examples/hello/hello.py
>>> hello()
hello
```

---
## 7) (Optional) Sync

After you’ve confirmed `generate` works:

```bash
pdd --force sync hello
```
---

## 8. What if nothing prints?

Sometimes the generated file only defines the function (e.g., `def hello(): print("hello")`) but doesn’t include the standard Python entry point:

```python
if __name__ == "__main__":
    hello()
```

In that case you have two options:

### Option A — Run interactively
```bash
python -i examples/hello/hello.py
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
python examples/hello/hello.py
# output:
hello
```


✅ That’s it! You’ve installed PDD, configured Gemini, set up the model CSV, and generated your first working example.
