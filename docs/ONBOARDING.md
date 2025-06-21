# PDD Onboarding Guide

This guide will help you get started with PDD (Prompt Driven Development) by walking you through the necessary setup steps.

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

### 2. Install PDD-CLI

Using UV, install the PDD CLI tool:

```bash
uv tool install pdd-cli
```

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

1. Open Cursor
2. Go to the Extensions marketplace
3. Search for ".prompt" by gltanaka
4. Click "Install"

### 7. Set Up Infisical

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

1. Check the [README](https://github.com/gltanaka/pdd/blob/main/README.md)
2. Search existing issues on GitHub
3. Join the [Discord](https://discord.gg/Q7Ts5Qt3) community for support
