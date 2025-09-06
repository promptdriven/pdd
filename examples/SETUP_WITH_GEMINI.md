# Getting Started with PDD using a Free Gemini API Key

This example shows you how to set up **Prompt-Driven Development (PDD)** with a free Google **Gemini API key** and run the built-in **Hello** example.

> Goal: By the end, you’ll have PDD installed, Gemini configured, and `pdd sync` running on the Hello example.

---

## 1. Install the `pdd` CLI

PDD works best if installed in an isolated environment. You can pick one of these methods:

### Option A — uv (recommended)
- **macOS/Linux**

  ```bash
  curl -LsSf https://astral.sh/uv/install.sh | sh
  ~/.local/bin/uv tool install pdd-cli
  ~/.local/bin/pdd --version

** Windows (PowerShell) ** 

powershell

irm https://astral.sh/uv/install.ps1 | iex
uv tool install pdd-cli
pdd --version

Option B — pipx

python -m pip install --user pipx
python -m pipx ensurepath
pipx install pdd-cli
pdd --version


Option C — venv

python -m venv ~/.venvs/pdd
source ~/.venvs/pdd/bin/activate   # Windows: %USERPROFILE%\venvs\pdd\Scripts\activate
pip install --upgrade pip
pip install pdd-cli
pdd --version

If you see pdd, version X.Y.Z, installation worked.
If pdd isn’t found, try ~/.local/bin/pdd --version once, then add ~/.local/bin to your PATH.

2. Create a Free Gemini API Key
Go to Google AI Studio.
https://aistudio.google.com/app/apikey

Log in with your Google account.

Click Create API key.

Copy the key.

3. Configure the API Key
macOS/Linux (bash/zsh):

export GEMINI_API_KEY="PASTE_YOUR_KEY_HERE"
(Optional: add this line to ~/.zshrc so it’s always available)

Windows (PowerShell):

setx GEMINI_API_KEY "PASTE_YOUR_KEY_HERE"

Then close and reopen your terminal.

Quick check:


# macOS/Linux
echo $GEMINI_API_KEY
# Windows
echo $Env:GEMINI_API_KEY


4. Run the Hello Example
Clone the repo and navigate into the Hello example:


git clone https://github.com/promptdriven/pdd.git
cd pdd/examples/hello

Now run:

pdd sync hello
👉 Important: pdd sync requires the basename of the file (without .py).

If the file is hello.py, the command is pdd sync hello.

5. Expected Output
You should see logs similar to:


No local LLM model CSV found, will use package default
LiteLLM disk cache configured at .../litellm_cache.sqlite
And PDD will generate or update:

test_hello.py
example JSON/artifacts

Troubleshooting
pdd: command not found
Add ~/.local/bin to your PATH or call with full path:
~/.local/bin/pdd sync hello

Gemini key not found

On macOS/Linux:

echo $GEMINI_API_KEY

On Windows:


echo $Env:GEMINI_API_KEY
Make sure you reopened your terminal after setx.

Conda errors
Don’t install into Conda base. Use uv or pipx for isolation.

