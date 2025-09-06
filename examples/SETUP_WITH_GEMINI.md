# Getting Started with PDD using a Free Gemini API Key

This example shows you how to set up **Prompt-Driven Development (PDD)** with a free Google **Gemini API key** and run the built-in **Hello** example.

> **Goal:** By the end, you’ll have PDD installed, Gemini configured, and `pdd sync` running on the Hello example.

---

## 1. Install the `pdd` CLI

PDD works best if installed in an isolated environment. You can pick one of these methods:

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

## 2. Create a Free Gemini API Key

1. Go to [Google AI Studio](https://aistudio.google.com/app/apikey).  
2. Log in with your Google account.  
3. Click **Create API key**.  
4. Copy the key.

---

## 3. Configure the API Key

**macOS/Linux (bash/zsh)**
```bash
export GEMINI_API_KEY="PASTE_YOUR_KEY_HERE"
```
*(Optional: add this line to `~/.zshrc` so it’s always available.)*

**Windows (PowerShell)**
```powershell
setx GEMINI_API_KEY "PASTE_YOUR_KEY_HERE"
```

Then close and reopen your terminal.

Quick check:
```bash
# macOS/Linux
echo $GEMINI_API_KEY
# Windows
echo $Env:GEMINI_API_KEY
```

---

## 4. Run the Hello Example

Clone the repo and navigate into the Hello example:
```bash
git clone https://github.com/promptdriven/pdd.git
cd pdd/examples/hello
```

Now run:
```bash
pdd sync hello
```

👉 **Important:** `pdd sync` requires the **basename** of the file (without `.py`).  
If the file is `hello.py`, the command is:
```bash
pdd sync hello
```

---

## 5. Expected Output

You should see logs similar to:
```
No local LLM model CSV found, will use package default
LiteLLM disk cache configured at .../litellm_cache.sqlite
```

And PDD will generate or update:
- `test_hello.py`
- Example JSON/artifacts

---

## Troubleshooting

**`pdd: command not found`**  
Add `~/.local/bin` to your PATH or call with full path:
```bash
~/.local/bin/pdd sync hello
```

**Gemini key not found**  
On macOS/Linux:
```bash
echo $GEMINI_API_KEY
```
On Windows:
```powershell
echo $Env:GEMINI_API_KEY
```
Make sure you reopened your terminal after `setx`.

**Conda errors**  
Don’t install into Conda base. Use **uv** or **pipx** for isolation.

---

✅ That’s it! You’ve successfully installed PDD, configured Gemini, and run your first example.  
Next, try editing the Hello example or running other ones in the `examples/` folder.
