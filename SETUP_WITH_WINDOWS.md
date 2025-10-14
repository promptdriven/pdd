# Getting Started with PDD on Windows

This example shows you how to set up **Prompt-Driven Development (PDD)** with **Windows** and run the built-in **Hello** example.

> **Goal:** By the end, you’ll have PDD installed on Windows and `pdd generate` running on the Hello example.

---

## 1. Install the `pdd` CLI

PDD runs on Python 3.8+, so verify its installation and add to PATH.    
You can verify this with:

```powershell  
python --version  
```

PDD works best in an isolated environment. You can pick one of these methods:

### Option A — uv (recommended)

**PowerShell**  
```powershell  
irm https://astral.sh/uv/install.ps1 | iex  
uv tool install pdd-cli  
pdd --version  
```

**Git Bash**  
```bash  
curl -LsSf https://astral.sh/uv/install.sh | sh  
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
%USERPROFILE%\venvs\pdd\Scripts\activate  
pip install --upgrade pip  
pip install pdd-cli  
pdd --version  
```

✅ If you see `pdd, version X.Y.Z`, installation worked.    
⚠️ If `pdd` isn’t found, try `~/.local/bin/pdd --version` once, then add `~/.local/bin` to your `PATH`.

---

## 2. Run the guided setup

With the CLI on your `PATH`, continue with:  
```bash  
pdd setup  
```  
The command installs tab completion, walks you through API key entry, and seeds local configuration files.  
If you postpone this step, the CLI detects the missing setup artifacts the first time you run another command and shows a reminder banner so you can complete it later (the banner is suppressed once `~/.pdd/api-env` exists or when your project already provides credentials via `.env` or `.pdd/`).

⚠️ If you see:  
```bash  
Unsupported shell:  
Error during ‘setup’ command:  
    An unexpected error occurred:  
```  
It means your `SHELL` environment variable is missing or invalid and must be set:

```bash  
# PowerShell  
$env:SHELL = "C:\Path\To\bash.exe"

# CMD  
set SHELL=C:\Path\To\bash.exe

# Git Bash  
export SHELL="/Path/To/bash"  
```

💡 These fixes only last for the current session.  
To make them permanent, add the variable to your system environment variables:

1. Search “Environment Variables” in the Start Menu

2. Click “Edit the system environment variables” → Environment Variables… 

3. Under “User variables for (username)” click New…  
    Variable name: SHELL  
    Variable value: Path to your shell executable (e.g., C:\Path\To\bash.exe)

---

## 3. Clone the repo

```bash  
git clone https://github.com/promptdriven/pdd.git  
cd pdd/examples/hello  
```  
Set environment variable PDD_PATH to the location of the cloned repo.

If you are having trouble with API keys, check out README.md or SETUP_WITH_GEMINI.md for more setup information.

---

## 4. Run the Hello example

From `pdd/examples/hello`:

```bash  
# generate code from the prompt  
pdd generate hello_python.prompt

# run the generated example if it has a main block  
python examples/hello/hello.py  
```

Sometimes the generated file only defines the function (e.g., `def hello(): print("hello")`) but doesn’t include the standard Python entry point:  
```python  
if __name__ == "__main__":  
    hello()  
```  
If the generated `hello.py` is minimal (no `__main__` block):

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

---

## 5. (Optional) Sync

After you’ve confirmed `generate` works:

```bash  
pdd --force sync hello  
```

---

## 6. Updating

If you are prompted to update to a new version of pdd-cli, the command may not work. Instead, use the following line to update:  
```bash  
uv tool upgrade pdd-cli  
```

✅ That’s it! You’ve installed PDD on Windows and generated your first working example.  
