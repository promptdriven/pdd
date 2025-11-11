// example/extension.ts
// Concise usage example for the PddInstaller module inside a VS Code extension.

import * as vscode from 'vscode';
import { PddInstaller } from './pddInstaller'; // adjust the relative path to where you placed the module

/**
 * VS Code extension activation entry point.
 *
 * Parameters:
 * - context: vscode.ExtensionContext
 *   VS Code provides this on activation. It holds global state, subscriptions,
 *   storage paths, and is passed to PddInstaller (optional) for any future use.
 *
 * Returns:
 * - void (Promise<void>)
 *   This function is awaited by VS Code. It should register commands and
 *   perform any one-time initialization.
 *
 * Behavior:
 * - Instantiates PddInstaller
 * - Triggers a best-effort auto-check and prompt to install PDD CLI if missing
 * - Registers commands that demonstrate how to call PddInstaller APIs
 */
export async function activate(context: vscode.ExtensionContext): Promise<void> {
  const installer = new PddInstaller(context);

  // 1) Optional: on activation, check and prompt to install PDD CLI if not present.
  //    This call is safe and silent on error by design.
  await installer.checkAndPromptInstallation();

  // 2) Register commands demonstrating proper usage.

  /**
   * Command: pdd.installCli
   * Input: none
   * Output: none (Promise<void>)
   * Behavior:
   * - Prompts for install method (uv recommended, pip as fallback)
   * - Shows progress and installs PDD CLI
   * - Presents post-install actions (open terminal, run setup, docs)
   */
  context.subscriptions.push(
    vscode.commands.registerCommand('pdd.installCli', async () => {
      await installer.installPddCli();
    })
  );

  /**
   * Command: pdd.runSetup
   * Input: none
   * Output: none (Promise<void>)
   * Behavior:
   * - Opens an integrated terminal and runs the PDD setup flow
   * - If a conda "pdd" env is found, activates it before running setup
   * - Otherwise tries uv tool path, uv tool run, then PATH "pdd"
   */
  context.subscriptions.push(
    vscode.commands.registerCommand('pdd.runSetup', async () => {
      await installer.runPddSetup();
    })
  );

  /**
   * Command: pdd.upgradeToUv
   * Input: none
   * Output: none (Promise<void>)
   * Behavior:
   * - Verifies PDD is installed
   * - Ensures uv is available (installs if needed)
   * - Uninstalls existing PDD (best effort) and reinstalls via uv
   */
  context.subscriptions.push(
    vscode.commands.registerCommand('pdd.upgradeToUv', async () => {
      await installer.upgradeToUvInstallation();
    })
  );

  /**
   * Command: pdd.isInstalled
   * Input: none
   * Output: void (shows a UI toast with the result)
   * Behavior:
   * - Uses isPddCliInstalled() to check for PDD CLI across multiple strategies
   * - Displays the result
   */
  context.subscriptions.push(
    vscode.commands.registerCommand('pdd.isInstalled', async () => {
      const installed = await installer.isPddCliInstalled();
      vscode.window.showInformationMessage(
        installed ? 'PDD CLI is installed.' : 'PDD CLI is not installed.'
      );
    })
  );
}

/**
 * VS Code extension deactivation entry point.
 *
 * Parameters: none
 * Returns: void
 * Behavior:
 * - Clean up resources if needed (not required for this example).
 */
export function deactivate(): void {
  // No-op
}

/**
How to wire commands in package.json (summary):
- Contributes four commands you can trigger from the Command Palette.
- Example labels and categories shown below.

"contributes": {
  "commands": [
    { "command": "pdd.installCli", "title": "PDD: Install PDD CLI", "category": "PDD" },
    { "command": "pdd.runSetup", "title": "PDD: Run PDD Setup", "category": "PDD" },
    { "command": "pdd.upgradeToUv", "title": "PDD: Upgrade PDD CLI to uv", "category": "PDD" },
    { "command": "pdd.isInstalled", "title": "PDD: Check if PDD CLI is Installed", "category": "PDD" }
  ]
}

Notes on PddInstaller methods you’ll call:
- new PddInstaller(context?)
  Input:
    - context?: vscode.ExtensionContext (optional)
  Output:
    - Instance of PddInstaller
  Behavior:
    - Stores context for potential future use.

- isPddCliInstalled(): Promise<boolean>
  Input:
    - none
  Output:
    - boolean indicating presence of PDD CLI via PATH, uv tool path/run, conda, or common paths.

- installPddCli(): Promise<void>
  Input:
    - none
  Output:
    - void
  Behavior:
    - Interactively installs via uv (preferred) or pip fallback. Shows progress and success actions.

- runPddSetup(): Promise<void>
  Input:
    - none
  Output:
    - void
  Behavior:
    - Opens integrated terminal and runs "pdd setup" with best-available path/env resolution.

- upgradeToUvInstallation(): Promise<void>
  Input:
    - none
  Output:
    - void
  Behavior:
    - Reinstalls PDD via uv, optionally installing uv first and removing prior pip/conda installs.
*/