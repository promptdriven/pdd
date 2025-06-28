# PDD Onboarding Guide

This guide provides instructions for setting up the Prompt-Driven Development (PDD) toolkit. It includes a quick start for users and a comprehensive guide for developers contributing to the project.

## Prerequisites

- A GitHub account
- Basic knowledge of command line operations
- Windows, macOS, or Linux operating system

## Installation Steps

### 1. Install UV Tool

UV is a Python package installer and resolver. Install it using one of the following methods:

**Windows (PowerShell):**
```powershell
(Invoke-WebRequest -Uri "https://astral.sh/uv/install.ps1" -UseBasicParsing).Content | pwsh -Command -
```

**macOS/Linux:**
```bash
curl -LsSf https://astral.sh/uv/install.sh | sh
```
*Note: You may need to restart your terminal or source your shell profile for the `uv` command to become available.*

### 2. Install PDD-CLI

Using UV, install the PDD CLI tool:

```bash
uv tool install pdd-cli
```
*Note: If the `pdd` command is not found after installation, try restarting your terminal.*

To verify your setup is complete, run:

```bash
pdd --version
```


### 3. Clone the GitHub Repository

```bash
git clone https://github.com/gltanaka/pdd.git
cd pdd
```

### 4. Review Documentation

1. Read through the [PDD Whitepaper](https://www.notion.so/Whitepaper-The-Case-for-Prompt-Driven-Development-1efd44f08ca480ac987ae068f2578f83) to understand the core concepts and architecture
2. Review the [main README.md](https://github.com/gltanaka/pdd/blob/main/README.md) for project overview and setup instructions

### 5. Set Up Cursor IDE

1. Visit [Cursor.sh](https://cursor.sh) and sign up for a trial account
2. Download and install Cursor for your operating system
3. Launch Cursor and sign in with your account

### 6. Install .prompt Extension

1. Find and download the `prompt-0.0.1.vsix` file from Slack
2. Open Cursor
3. Open the command palette:
   - Use `Ctrl+Shift+P` (or `Cmd+Shift+P` on macOS)
4. Type "Extensions: Install from VSIX" and select it
5. Locate and select the `prompt-0.0.1.vsix` file you downloaded
6. Confirm the installation. You may need to reload the window to activate it.

1.  **Locate the Extension:** The extension file (`prompt-*.vsix`) is located in the `dist/` directory of this repository. Alternatively, it can be downloaded from the project's [GitHub Releases](https://github.com/gltanaka/pdd/releases).
2.  **Open Cursor** and the command palette (`Ctrl+Shift+P` or `Cmd+Shift+P`).
3.  Type and select **"Extensions: Install from VSIX..."**
4.  Locate and select the `prompt-*.vsix` file to install it.

### 7. Set Up Infisical for Secrets Management

1. Install Infisical CLI:

   **Windows (PowerShell):**
   ```powershell
   winget install infisical
   ```

   **macOS:**
   ```bash
   brew install infisical
   ```

   **Linux:**
   ```bash
   curl -fsSL https://infisical.com/install.sh | sh
   ```

2. Accept Project Invitation:
   - Check your email for an invitation to the PDD project in Infisical
   - Click the invitation link and accept the project
   - Verify that you can see the `PDD-secrets` project in your Infisical dashboard

3. Authenticate and Link:
   ```bash
   # Login to Infisical
   infisical login
   
   # Link the project (run this in your PDD project directory)
   infisical init
   ```

## Next Steps

- Join the PDD community on Discord
- Review example projects in the `examples/` directory
- Start with the basic tutorials in the documentation

## Troubleshooting

If you encounter any issues during setup:

1. Re-read the instructions carefully.
2. Check the [README](https://github.com/gltanaka/pdd/blob/main/README.md) for additional details.
3. Search existing issues on GitHub.
4. Join the [Discord](https://discord.gg/Q7Ts5Qt3) community for support.

---

## Appendix: Advanced Setup for Local Development (including WSL)

The steps below are **required** for developers who want to contribute code, run the test suite, and work on PDD locally.

### For Windows Users: Install WSL

If you are on Windows, you **must** use the Windows Subsystem for Linux (WSL) to run project commands like `make test`.

-   **Action:** Install WSL by following the [official Microsoft guide](https://learn.microsoft.com/en-us/windows/wsl/install). An Ubuntu distribution is recommended.
-   **Important:** For optimal performance, clone the repository and run all subsequent commands **inside your WSL home directory (`~/`)**, not on a mounted Windows drive (`/mnt/c/...`).

### Environment Setup with Conda

The development environment relies on Conda to manage Python versions and dependencies.

1.  **Install Anaconda/Miniconda:** Follow the official instructions on the [Anaconda website](https://www.anaconda.com/products/distribution).
2.  **Create and Activate Conda Environment:**
    ```bash
    # Create the environment
    conda create --name pdd python=3.11 -y

    # Activate the environment
    conda activate pdd
    ```
    *You must activate this environment whenever you work on the project. Your terminal prompt should now be prefixed with `(pdd)`.*

3. **Install Project Dependencies:**
   With the `pdd` environment active, install the required Python packages and the project in editable mode from the project root.
   ```bash
   pip install -r requirements.txt
   pip install -e .
   ```
   *Installing with `-e .` (editable mode) is crucial for development, as it makes your changes to the source code take effect without needing to reinstall the package.*

### Running Commands with Secrets

Any command that requires API keys (like `make test`) must be run using the `infisical run` wrapper, which injects the secrets into the command's environment.

- **Example:**
  ```bash
  infisical run -- make test
  ```

### Final Project Configuration

These final steps configure the local repository to ensure the application can find its resources correctly.

**1. Create Symbolic Links:**
The application's source code in `pdd/` needs access to the project's root `prompts/` and `data/` directories. This step creates symbolic links to make them accessible.

```bash
# Navigate into the pdd directory
cd pdd

# Remove the existing prompts and data files in the pdd folder
rm -f prompts
rm -f data

# Link to the root prompts/ and data/ directories
# (use rm -rf if they already exist as regular directories)
ln -s ../prompts .
rm -f prompts
rm -f data
# Go back to the project root
cd ..
```

**2. Set the `PDD_PATH` Environment Variable:**
The application needs the absolute path to the `pdd/` source directory to function correctly.

-   **Step 1: Get the path.**
    From the project root, run:
    ```bash
    cd pdd
    pwd  # Copy the full path output by this command
    cd ..
    ```
-   **Step 2: Create a local `.env` file.** The `infisical run` command loads this file automatically, making the variable available.
    ```bash
    # Replace "/path/to/your/project/pdd" with the path you copied
    echo "PDD_PATH=/path/to/your/project/pdd" > .env
    ```
-   **Step 3: Update `.gitignore`** to ensure this local configuration file is not committed to version control.
    ```bash
    echo ".env" >> .gitignore
    ```

	**3. Set Conda Environment Variable (Recommended for WSL):**
This is the most robust method to ensure `PDD_PATH` is always set correctly when your Conda environment is active, as it takes precedence over system variables within the Conda shell.
-   **Step 1: Set the Conda variable.**
    Using the same absolute path you copied in Step 2.1 (`/path/to/your/project/pdd`), run the following command from your project root:
    ```bash
    # Replace "/path/to/your/project/pdd" with the correct path
    conda env config vars set PDD_PATH="/path/to/your/project/pdd"
    ```
-   **Step 2: Reactivate the environment.**
    The change will only take effect after you deactivate and reactivate your environment.
    ```bash
    conda deactivate
    conda activate pdd
    ```
-   **Step 3: Verify the change.**
    You can now check if the path is set correctly.
    ```bash
    echo $PDD_PATH
    # It should print the correct path: /path/to/your/project/pdd
    ```
