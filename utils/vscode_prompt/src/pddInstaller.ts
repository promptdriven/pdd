import * as vscode from 'vscode';
import * as cp from 'child_process';
import { promisify } from 'util';

const exec = promisify(cp.exec);

export class PddInstaller {
  private readonly context?: vscode.ExtensionContext;

  constructor(context?: vscode.ExtensionContext) {
    this.context = context;
  }

  async isPddCliInstalled(): Promise<boolean> {
    console.log('PDD: Checking if PDD CLI is installed...');
    const home = process.env.HOME || '';
    const isWin = process.platform === 'win32';

    const tryCommand = async (cmd: string, label?: string): Promise<boolean> => {
      try {
        console.log(`PDD: Detecting via ${label || cmd}`);
        const { stdout, stderr } = await exec(cmd);
        console.log(`PDD: Success (${label || cmd}) stdout: ${stdout?.trim()} stderr: ${stderr?.trim()}`);
        return true;
      } catch (err: any) {
        console.log(`PDD: Detection failed for ${label || cmd}: ${err?.message || err}`);
        return false;
      }
    };

    // 1) Standard PATH
    if (await tryCommand('pdd --version', 'PATH pdd')) return true;

    // 2) uv tool path
    const uvPddPath = `${home}/.local/share/uv/tools/pdd-cli/bin/pdd`;
    if (await tryCommand(`"${this.expandPath(uvPddPath)}" --version`, 'uv tool path pdd')) return true;

    // 3) uv tool run
    if (await tryCommand('uv tool run pdd-cli --version', 'uv tool run pdd-cli')) return true;

    // 4) conda run fallback
    if (await tryCommand('conda run -n pdd pdd --version', 'conda run fallback')) return true;

    // 5) common paths
    const candidates = [
      `${home}/.local/bin/pdd`,
      '/opt/anaconda3/bin/pdd',
      '/opt/miniconda3/bin/pdd',
      `${home}/anaconda3/bin/pdd`,
      `${home}/miniconda3/bin/pdd`,
    ];
    for (const p of candidates) {
      if (await tryCommand(`"${this.expandPath(p)}" --version`, `common path ${p}`)) return true;
    }

    console.log('PDD: PDD CLI not detected by any method.');
    return false;
  }

  async installPddCli(): Promise<void> {
    try {
      console.log('PDD: Starting PDD CLI installation flow.');
      const choice = await vscode.window.showInformationMessage(
        'Install PDD CLI?',
        { modal: false, detail: 'PDD CLI will be installed using uv (the modern Python package manager). If uv is not installed, it will be installed first.' },
        'Install PDD CLI',
        'Cancel'
      );

      if (!choice || choice === 'Cancel') {
        console.log('PDD: User cancelled installation.');
        vscode.window.showInformationMessage('PDD CLI installation was cancelled.');
        return;
      }

      console.log('PDD: User confirmed installation.');

      let method: 'uv' | 'uv-installed' = 'uv';

      await vscode.window.withProgress(
        {
          location: vscode.ProgressLocation.Notification,
          title: 'Installing PDD CLI',
          cancellable: false,
        },
        async (progress) => {
          const report = (pct: number, message: string) => {
            progress.report({ increment: pct, message });
            console.log(`PDD: ${message} (${pct}%)`);
          };

          report(0, 'Installing PDD CLI...');

          // Check uv availability
          let uvAvailable = await this.commandExists('uv --version');
          if (!uvAvailable) {
            // install uv
            report(10, 'Installing uv package manager...');
            await this.installUv();
            report(15, 'uv installed! Now installing PDD CLI...');
            uvAvailable = true;
            method = 'uv-installed';
          }

          // Install pdd-cli via uv
          try {
            report(25, 'Installing PDD CLI package...');
            await this.runWithShellLogging('uv tool install pdd-cli', 'uv tool install pdd-cli');
            if (method !== 'uv-installed') method = 'uv';
          } catch (eUv: any) {
            console.warn('PDD: uv install via PATH failed. Trying full path.', eUv);
            const uvFullPath = this.getUvFullPath();
            await this.runWithShellLogging(`"${uvFullPath}" tool install pdd-cli`, 'uv fullpath tool install pdd-cli');
            if (method !== 'uv-installed') method = 'uv';
          }

          report(100, 'PDD CLI installed successfully!');
        }
      );

      // Success messaging and actions
      if (method === 'uv') {
        const btn = await vscode.window.showInformationMessage(
          'PDD CLI has been installed successfully using uv! Run "pdd setup" in your terminal or use the "PDD: Run PDD Setup" command to configure API keys and install tab completion.',
          'Open Terminal',
          'Run Setup',
          'View PDD Docs',
          'View uv Docs'
        );
        await this.handleSuccessButtons(btn);
      } else if (method === 'uv-installed') {
        const btn = await vscode.window.showInformationMessage(
          'PDD CLI has been installed successfully! We also installed uv (the modern Python package manager) for future use. Run "pdd setup" in your terminal or use the "PDD: Run PDD Setup" command to configure API keys and install tab completion.',
          'Open Terminal',
          'Run Setup',
          'View PDD Docs',
          'View uv Docs'
        );
        await this.handleSuccessButtons(btn);
      }
    } catch (err: any) {
      console.error('PDD: Failed to install PDD CLI:', err);
      vscode.window.showErrorMessage(
        `Failed to install PDD CLI: ${err?.message || String(err)}. Please install manually: uv tool install pdd-cli`
      );
    }
  }

  async runPddSetup(): Promise<void> {
    try {
      console.log('PDD: Running PDD setup in integrated terminal.');
      const term = vscode.window.createTerminal('PDD Setup');
      term.show();

      const reloadNote = ' && echo "Setup complete! Please reload your shell: source ~/.zshrc (or ~/.bashrc)"';

      // Try known uv tool path then uv tool run, else pdd in PATH
      const uvPddPath = this.expandPath(`${process.env.HOME || ''}/.local/share/uv/tools/pdd-cli/bin/pdd`);
      const uvPathCheck = await this.commandExists(`"${uvPddPath}" --version`);
      if (uvPathCheck) {
        term.sendText(`"${uvPddPath}" setup${reloadNote}`);
      } else if (await this.commandExists('uv --version')) {
        term.sendText(`uv tool run pdd-cli setup${reloadNote}`);
      } else {
        term.sendText(`pdd setup${reloadNote}`);
      }

      vscode.window.showInformationMessage(
        'PDD setup is running in the terminal. Follow the prompts to configure your API keys, then reload your shell for tab completion.'
      );
    } catch (err: any) {
      console.error('PDD: Failed to run PDD setup:', err);
      vscode.window.showErrorMessage(`Failed to run PDD setup: ${err?.message || String(err)}`);
    }
  }

  async upgradeToUvInstallation(): Promise<void> {
    try {
      console.log('PDD: Upgrade to uv installation initiated.');
      const installed = await this.isPddCliInstalled();
      if (!installed) {
        vscode.window.showWarningMessage('PDD CLI is not installed. Use "PDD: Install PDD CLI" command instead.');
        return;
      }

      let uvAvailable = await this.commandExists('uv --version');
      if (uvAvailable) {
        // Check if already installed via uv
        try {
          const { stdout } = await exec('uv tool list');
          if (/pdd-cli/i.test(stdout)) {
            vscode.window.showInformationMessage('PDD CLI is already installed via uv!');
            return;
          }
        } catch (e) {
          console.warn('PDD: Failed to check uv tool list.', e);
        }
      } else {
        const resp = await vscode.window.showInformationMessage(
          'To upgrade to uv installation, we first need to install uv (the modern Python package manager). This will give you access to the latest PDD CLI features and faster updates.',
          { modal: true },
          'Install uv and upgrade',
          'Cancel'
        );
        if (resp !== 'Install uv and upgrade') {
          console.log('PDD: User cancelled uv installation for upgrade.');
          return;
        }
      }

      const confirm = await vscode.window.showInformationMessage(
        'Upgrade PDD CLI to uv installation?\n\n✅ Benefits:\n• Latest PDD CLI version\n• Faster updates\n• Better dependency management\n• Isolated installation\n\n⚠️ Your current PDD installation will be removed and reinstalled via uv.',
        { modal: true },
        'Yes, upgrade to uv',
        'No, keep current installation'
      );
      if (confirm !== 'Yes, upgrade to uv') {
        console.log('PDD: User chose not to upgrade.');
        return;
      }

      await vscode.window.withProgress(
        {
          location: vscode.ProgressLocation.Notification,
          title: 'Upgrading PDD CLI to uv',
          cancellable: false,
        },
        async (progress) => {
          const report = (pct: number, message: string) => {
            progress.report({ increment: pct, message });
            console.log(`PDD: ${message} (${pct}%)`);
          };

          // Ensure uv installed
          if (!uvAvailable) {
            report(0, 'Installing uv...');
            await this.installUv();
            uvAvailable = true;
            report(20, 'uv installed!');
          } else {
            report(20, 'uv is available');
          }

          // Remove old installation (best-effort)
          report(20, 'Removing old PDD installation...');
          try {
            await this.runWithShellLogging('pip uninstall pdd-cli -y', 'pip uninstall pdd-cli');
          } catch (e) {
            console.warn('PDD: pip uninstall failed. Continuing anyway.', e);
          }

          // Install via uv
          report(30, 'Installing PDD CLI via uv...');
          try {
            await this.runWithShellLogging('uv tool install pdd-cli', 'uv tool install pdd-cli');
          } catch (eUv: any) {
            console.warn('PDD: uv install via PATH failed. Trying full path.', eUv);
            const uvFullPath = this.getUvFullPath();
            await this.runWithShellLogging(`"${uvFullPath}" tool install pdd-cli`, 'uv fullpath tool install pdd-cli');
          }

          report(70, 'Upgrade complete!');
        }
      );

      const btn = await vscode.window.showInformationMessage(
        'PDD CLI has been successfully upgraded to uv installation! You now have access to the latest features and faster updates.',
        'View uv Docs',
        'OK'
      );
      if (btn === 'View uv Docs') {
        vscode.env.openExternal(vscode.Uri.parse('https://docs.astral.sh/uv/'));
      }
    } catch (err: any) {
      console.error('PDD: Failed to upgrade PDD CLI to uv:', err);
      vscode.window.showErrorMessage(`Failed to upgrade PDD CLI to uv: ${err?.message || String(err)}`);
    }
  }

  async checkAndPromptInstallation(): Promise<void> {
    try {
      const config = vscode.workspace.getConfiguration('pdd');
      const promptEnabled = config.get<boolean>('promptForInstallation', true);
      console.log(`PDD: checkAndPromptInstallation - prompt enabled: ${promptEnabled}`);
      if (!promptEnabled) {
        console.log('PDD: Prompting disabled by user setting.');
        return;
      }

      const installed = await this.isPddCliInstalled();
      console.log(`PDD: PDD CLI installed: ${installed}`);
      if (!installed) {
        const choice = await vscode.window.showInformationMessage(
          'PDD CLI is not installed. Would you like to install it automatically?',
          'Install PDD CLI',
          'Not Now',
          "Don't Ask Again"
        );
        if (choice === 'Install PDD CLI') {
          await this.installPddCli();
        } else if (choice === "Don't Ask Again") {
          await config.update('promptForInstallation', false, vscode.ConfigurationTarget.Global);
          console.log('PDD: Disabled future installation prompts.');
        }
      }
    } catch (err) {
      console.error('PDD: Silent failure in checkAndPromptInstallation:', err);
      // Silent failure by design
    }
  }

  // Helpers

  private expandPath(p: string): string {
    if (!p) return p;
    if (p.startsWith('~')) {
      const home = process.env.HOME || '';
      return p.replace(/^~/, home);
    }
    return p;
  }

  private async commandExists(cmd: string): Promise<boolean> {
    try {
      await exec(cmd);
      return true;
    } catch {
      return false;
    }
  }

  private async installUv(): Promise<void> {
    const isWin = process.platform === 'win32';
    const cmd = isWin
      ? 'powershell -c "irm https://astral.sh/uv/install.ps1 | iex"'
      : 'curl -LsSf https://astral.sh/uv/install.sh | sh';
    console.log(`PDD: Installing uv with: ${cmd}`);
    await this.runWithShellLogging(cmd, 'install uv');
  }

  private getUvFullPath(): string {
    const isWin = process.platform === 'win32';
    if (isWin) {
      const userProfile = process.env.USERPROFILE || '';
      return `${userProfile}\\.cargo\\bin\\uv`;
    }
    const home = process.env.HOME || '';
    return `${home}/.cargo/bin/uv`;
  }

  private async runWithShellLogging(command: string, label?: string): Promise<{ stdout: string; stderr: string }> {
    console.log(`PDD: Running command${label ? ` [${label}]` : ''}: ${command}`);
    const res = await exec(command);
    if (res.stdout) console.log(`PDD: ${label || 'cmd'} stdout:\n${res.stdout}`);
    if (res.stderr) console.log(`PDD: ${label || 'cmd'} stderr:\n${res.stderr}`);
    return res;
  }

  private async handleSuccessButtons(btn?: string): Promise<void> {
    if (btn === 'Open Terminal') {
      vscode.commands.executeCommand('workbench.action.terminal.new');
    } else if (btn === 'Run Setup') {
      await this.runPddSetup();
    } else if (btn === 'View PDD Docs') {
      vscode.env.openExternal(vscode.Uri.parse('https://github.com/promptdriven/pdd#readme'));
    } else if (btn === 'View uv Docs') {
      vscode.env.openExternal(vscode.Uri.parse('https://docs.astral.sh/uv/'));
    }
  }
}
