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

### 5. Set Up Cursor IDE (*Optional but heavily recommended, Visual Studio Code or other similar IDE)

1. Visit [Cursor.sh](https://cursor.sh) and sign up for a trial account
2. Download and install Cursor for your operating system
3. Launch Cursor and sign in with your account

### 6. Install .prompt Extension

To enable syntax highlighting for `.prompt` files in your editor, you'll need to install the PDD extension.

1.  **Download the Extension:**
    -   Navigate to the [project's GitHub Releases page](https://github.com/gltanaka/pdd/releases).
    -   Download the latest version of the extension, which will be a file named `prompt-*.vsix`.

2.  **Install in your IDE:**
    -   Open your IDE (Cursor, VS Code, etc.).
    -   Open the command palette with `Ctrl+Shift+P` (or `Cmd+Shift+P` on macOS).
    -   Type `"Extensions: Install from VSIX..."` and select it.
    -   Locate the `prompt-*.vsix` file you downloaded and select it to complete the installation.

### 7. Set Up Infisical for Secrets Management (Recommended)

Managing API keys and other secrets securely is crucial. We recommend using [Infisical](https://infisical.com/) to handle your environment variables.

**1. Install the Infisical CLI:**

Choose the command for your operating system:

-   **Windows (PowerShell):**
    ```powershell
    winget install infisical
    ```
-   **macOS:**
    ```bash
    brew install infisical
    ```
-   **Linux:**
    ```bash
    curl -1sLf 'https://artifacts-cli.infisical.com/setup.deb.sh' | sudo -E bash
    ```

**2. Configure Your Project:**

You can either use your own Infisical project or join an existing one.

-   **To use your own project:**
    1.  Set up a new project in your Infisical dashboard.
    2.  Add all the API keys you intend to use with PDD.
    3.  Refer to the [Infisical Quick Start Guide](https://infisical.com/docs/cli/usage) for more details.
-   **To join an existing project:**
    1.  Check your email for an invitation.
    2.  Accept the invitation and ensure you can see the project in your dashboard.

**3. Authenticate and Link Your Local Repository:**

Run these commands in your terminal from the root of the `pdd` repository:

```bash
# Log in to your Infisical account
infisical login

# Link your local repo to the Infisical project
infisical init
```

**Important Notes on Secrets Management:**
- Using Infisical is the recommended way to manage secrets, as it avoids storing keys in plaintext files like `.env`.
- If you use a local `.env` file for non-secret values (e.g., local file paths), ensure that the keys do not overlap with any secret names in your Infisical project. In case of a name conflict, Infisical's values will take precedence.

Any command that requires API keys (like `make test`) should be run using the `infisical run` wrapper. This command injects the secrets from your Infisical project into the command's environment, making them securely available.

If your local `.env` file contains keys that are also present in your Infisical project, the values from Infisical will be used. Keys that exist only in your local `.env` file will also be loaded.

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
ln -s ../data .
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
-   **Step 2: Create a local `.env` file.** 
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
    Using the same absolute path you copied in Step 2.1 (`/path/to/your/project/pdd`), run the following command from your project root (using pwd):
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

---
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