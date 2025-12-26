
## MacOS Only Prerequisite - Python 3.0+
1. **Install Xcode Command Line Tools** (required for Python compilation):
   ```bash
   xcode-select --install
   ```

2. **Install Homebrew** (recommended package manager for macOS):
   ```bash
   /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
   ```
   
   After installation, add Homebrew to your PATH:
   ```bash
   echo 'eval "$(/opt/homebrew/bin/brew shellenv)"' >> ~/.zprofile && eval "$(/opt/homebrew/bin/brew shellenv)"
   ```

3. **Install Python** (if not already installed):
   ```bash
   # Check if Python is installed
   python3 --version
   
   # If Python is not found, install it via Homebrew
   brew install python
   ```
   
   **Note**: macOS comes with Python 2.7 by default (deprecated), but PDD requires Python 3.8 or higher. The `brew install python` command installs the latest Python 3 version.



## MacOS & Linux Prerequisites

#### Option 1: uv
```bash
curl -LsSf https://astral.sh/uv/install.sh | sh
```

#### Option 2: pip 
(after installing python via your preferred method, and ensuring that installed python is in your search path)
```bash
python3 -m ensurepip --upgrade
