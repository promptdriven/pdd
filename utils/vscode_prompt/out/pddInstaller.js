"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || function (mod) {
    if (mod && mod.__esModule) return mod;
    var result = {};
    if (mod != null) for (var k in mod) if (k !== "default" && Object.prototype.hasOwnProperty.call(mod, k)) __createBinding(result, mod, k);
    __setModuleDefault(result, mod);
    return result;
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.PddInstaller = void 0;
const vscode = __importStar(require("vscode"));
const cp = __importStar(require("child_process"));
const fs = __importStar(require("fs"));
const util_1 = require("util");
const exec = (0, util_1.promisify)(cp.exec);
class PddInstaller {
    constructor(context) {
        this.context = context;
    }
    async isPddCliInstalled() {
        console.log('PDD: Checking if PDD CLI is installed...');
        const isWin = process.platform === 'win32';
        const home = isWin ? (process.env.USERPROFILE || '') : (process.env.HOME || '');
        const tryCommand = async (cmd, label) => {
            try {
                console.log(`PDD: Detecting via ${label || cmd}`);
                const { stdout, stderr } = await exec(cmd);
                console.log(`PDD: Success (${label || cmd}) stdout: ${stdout?.trim()} stderr: ${stderr?.trim()}`);
                return true;
            }
            catch (err) {
                console.log(`PDD: Detection failed for ${label || cmd}: ${err?.message || err}`);
                return false;
            }
        };
        // 1) Standard PATH
        if (await tryCommand('pdd --version', 'PATH pdd'))
            return true;
        // 2) uv tool path (platform-specific)
        const uvPddPath = this.getUvToolPddPath();
        if (await tryCommand(`"${uvPddPath}" --version`, 'uv tool path pdd'))
            return true;
        // 3) uv tool run
        if (await tryCommand('uv tool run pdd-cli --version', 'uv tool run pdd-cli'))
            return true;
        // 4) common paths
        const candidates = isWin
            ? [
                `${home}\\.local\\bin\\pdd.exe`,
                `${home}\\AppData\\Local\\Programs\\Python\\Scripts\\pdd.exe`,
            ]
            : [
                `${home}/.local/bin/pdd`,
                '/opt/anaconda3/bin/pdd',
                '/opt/miniconda3/bin/pdd',
                `${home}/anaconda3/bin/pdd`,
                `${home}/miniconda3/bin/pdd`,
            ];
        for (const p of candidates) {
            if (await tryCommand(`"${this.expandPath(p)}" --version`, `common path ${p}`))
                return true;
        }
        console.log('PDD: PDD CLI not detected by any method.');
        return false;
    }
    async installPddCli() {
        try {
            console.log('PDD: Starting PDD CLI installation flow.');
            const choice = await vscode.window.showInformationMessage('Install PDD CLI?', { modal: false, detail: 'PDD CLI will be installed using uv (the modern Python package manager). If uv is not installed, it will be installed first.' }, 'Install PDD CLI', 'Cancel');
            if (!choice || choice === 'Cancel') {
                console.log('PDD: User cancelled installation.');
                vscode.window.showInformationMessage('PDD CLI installation was cancelled.');
                return;
            }
            console.log('PDD: User confirmed installation.');
            // Proceed with installation
            await this.installPddCliWithChoice('uv');
        }
        catch (err) {
            console.error('PDD: Failed to install PDD CLI:', err);
            vscode.window.showErrorMessage(`Failed to install PDD CLI: ${err?.message || String(err)}. Please install manually: uv tool install pdd-cli`);
        }
    }
    /**
     * Internal method to install PDD CLI using uv.
     * Used by checkAndPromptInstallation to avoid double prompts.
     */
    async installPddCliWithChoice(method) {
        let installMethod = 'uv';
        await vscode.window.withProgress({
            location: vscode.ProgressLocation.Notification,
            title: 'Installing PDD CLI',
            cancellable: false,
        }, async (progress) => {
            const report = (pct, message) => {
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
                installMethod = 'uv-installed';
            }
            // Install pdd-cli via uv
            try {
                report(25, 'Installing PDD CLI package...');
                await this.runWithShellLogging('uv tool install pdd-cli', 'uv tool install pdd-cli');
                if (installMethod !== 'uv-installed')
                    installMethod = 'uv';
            }
            catch (eUv) {
                console.warn('PDD: uv install via PATH failed. Trying full path.', eUv);
                const uvFullPath = this.getUvFullPath();
                await this.runWithShellLogging(`"${uvFullPath}" tool install pdd-cli`, 'uv fullpath tool install pdd-cli');
                if (installMethod !== 'uv-installed')
                    installMethod = 'uv';
            }
            report(100, 'PDD CLI installed successfully!');
        });
        // Success messaging and actions
        if (installMethod === 'uv') {
            const btn = await vscode.window.showInformationMessage('PDD CLI has been installed successfully using uv! Run "pdd setup" in your terminal or use the "PDD: Run PDD Setup" command to configure API keys and install tab completion.', 'Open Terminal', 'Run Setup', 'View PDD Docs', 'View uv Docs');
            await this.handleSuccessButtons(btn);
        }
        else if (installMethod === 'uv-installed') {
            const btn = await vscode.window.showInformationMessage('PDD CLI has been installed successfully! We also installed uv (the modern Python package manager) for future use. Run "pdd setup" in your terminal or use the "PDD: Run PDD Setup" command to configure API keys and install tab completion.', 'Open Terminal', 'Run Setup', 'View PDD Docs', 'View uv Docs');
            await this.handleSuccessButtons(btn);
        }
    }
    async runPddSetup() {
        try {
            console.log('PDD: Running PDD setup in integrated terminal.');
            await vscode.window.withProgress({
                location: vscode.ProgressLocation.Notification,
                title: 'Running PDD Setup',
                cancellable: false,
            }, async (progress) => {
                progress.report({ increment: 0, message: 'Opening terminal...' });
                const term = vscode.window.createTerminal('PDD Setup');
                term.show();
                const reloadNote = ' && echo "Setup complete! Please reload your shell: source ~/.zshrc (or ~/.bashrc)"';
                progress.report({ increment: 30, message: 'Detecting PDD CLI installation...' });
                // Try known uv tool path then uv tool run, else pdd in PATH
                const uvPddPath = this.getUvToolPddPath();
                const uvPathCheck = await this.commandExists(`"${uvPddPath}" --version`);
                progress.report({ increment: 50, message: 'Launching setup command...' });
                if (uvPathCheck) {
                    term.sendText(`"${uvPddPath}" setup${reloadNote}`);
                }
                else if (await this.commandExists('uv --version')) {
                    term.sendText(`uv tool run pdd-cli setup${reloadNote}`);
                }
                else {
                    term.sendText(`pdd setup${reloadNote}`);
                }
                progress.report({ increment: 20, message: 'Setup running in terminal...' });
            });
            vscode.window.showInformationMessage('PDD setup is running in the terminal. Follow the prompts to configure your API keys, then reload your shell for tab completion.');
        }
        catch (err) {
            console.error('PDD: Failed to run PDD setup:', err);
            vscode.window.showErrorMessage(`Failed to run PDD setup: ${err?.message || String(err)}`);
        }
    }
    async upgradeToUvInstallation() {
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
                }
                catch (e) {
                    console.warn('PDD: Failed to check uv tool list.', e);
                }
            }
            else {
                const resp = await vscode.window.showInformationMessage('To upgrade to uv installation, we first need to install uv (the modern Python package manager). This will give you access to the latest PDD CLI features and faster updates.', { modal: true }, 'Install uv and upgrade', 'Cancel');
                if (resp !== 'Install uv and upgrade') {
                    console.log('PDD: User cancelled uv installation for upgrade.');
                    return;
                }
            }
            const confirm = await vscode.window.showInformationMessage('Upgrade PDD CLI to uv installation?\n\n✅ Benefits:\n• Latest PDD CLI version\n• Faster updates\n• Better dependency management\n• Isolated installation\n\n⚠️ Your current PDD installation will be removed and reinstalled via uv.', { modal: true }, 'Yes, upgrade to uv', 'No, keep current installation');
            if (confirm !== 'Yes, upgrade to uv') {
                console.log('PDD: User chose not to upgrade.');
                return;
            }
            await vscode.window.withProgress({
                location: vscode.ProgressLocation.Notification,
                title: 'Upgrading PDD CLI to uv',
                cancellable: false,
            }, async (progress) => {
                const report = (pct, message) => {
                    progress.report({ increment: pct, message });
                    console.log(`PDD: ${message} (${pct}%)`);
                };
                // Ensure uv installed
                if (!uvAvailable) {
                    report(0, 'Installing uv...');
                    await this.installUv();
                    uvAvailable = true;
                    report(20, 'uv installed!');
                }
                else {
                    report(20, 'uv is available');
                }
                // Remove old installation (best-effort)
                report(20, 'Removing old PDD installation...');
                try {
                    await this.runWithShellLogging('pip uninstall pdd-cli -y', 'pip uninstall pdd-cli');
                }
                catch (e) {
                    console.warn('PDD: pip uninstall failed. Continuing anyway.', e);
                }
                // Install via uv
                report(30, 'Installing PDD CLI via uv...');
                try {
                    await this.runWithShellLogging('uv tool install pdd-cli', 'uv tool install pdd-cli');
                }
                catch (eUv) {
                    console.warn('PDD: uv install via PATH failed. Trying full path.', eUv);
                    const uvFullPath = this.getUvFullPath();
                    await this.runWithShellLogging(`"${uvFullPath}" tool install pdd-cli`, 'uv fullpath tool install pdd-cli');
                }
                report(100, 'Upgrade complete!');
            });
            const btn = await vscode.window.showInformationMessage('PDD CLI has been successfully upgraded to uv installation! You now have access to the latest features and faster updates.', 'View uv Docs', 'OK');
            if (btn === 'View uv Docs') {
                vscode.env.openExternal(vscode.Uri.parse('https://docs.astral.sh/uv/'));
            }
        }
        catch (err) {
            console.error('PDD: Failed to upgrade PDD CLI to uv:', err);
            vscode.window.showErrorMessage(`Failed to upgrade PDD CLI to uv: ${err?.message || String(err)}`);
        }
    }
    async checkAndPromptInstallation() {
        try {
            const config = vscode.workspace.getConfiguration('pdd');
            const promptEnabled = config.get('promptForInstallation', true);
            console.log(`PDD: checkAndPromptInstallation - prompt enabled: ${promptEnabled}`);
            if (!promptEnabled) {
                console.log('PDD: Prompting disabled by user setting.');
                return;
            }
            const installed = await this.isPddCliInstalled();
            console.log(`PDD: PDD CLI installed: ${installed}`);
            if (!installed) {
                // Show single consolidated prompt
                const choice = await vscode.window.showInformationMessage('PDD CLI is not installed. Would you like to install it?', {
                    modal: false,
                    detail: 'PDD CLI will be installed using uv (the modern Python package manager). If uv is not installed, it will be installed first.'
                }, 'Install PDD CLI', 'Not Now', "Don't Ask Again");
                if (choice === 'Install PDD CLI') {
                    // Call installPddCli with the user's choice already made
                    await this.installPddCliWithChoice('uv');
                }
                else if (choice === "Don't Ask Again") {
                    await config.update('promptForInstallation', false, vscode.ConfigurationTarget.Global);
                    console.log('PDD: Disabled future installation prompts.');
                }
            }
        }
        catch (err) {
            console.error('PDD: Silent failure in checkAndPromptInstallation:', err);
            // Silent failure by design
        }
    }
    // Helpers
    expandPath(p) {
        if (!p)
            return p;
        if (p.startsWith('~')) {
            const home = process.env.HOME || '';
            return p.replace(/^~/, home);
        }
        return p;
    }
    async commandExists(cmd) {
        try {
            await exec(cmd);
            return true;
        }
        catch {
            return false;
        }
    }
    async installUv() {
        const isWin = process.platform === 'win32';
        const cmd = isWin
            ? 'powershell -ExecutionPolicy Bypass -Command "irm https://astral.sh/uv/install.ps1 | iex"'
            : 'curl -LsSf https://astral.sh/uv/install.sh | sh';
        console.log(`PDD: Installing uv with: ${cmd}`);
        await this.runWithShellLogging(cmd, 'install uv');
    }
    getUvFullPath() {
        const isWin = process.platform === 'win32';
        const home = isWin ? (process.env.USERPROFILE || '') : (process.env.HOME || '');
        if (isWin) {
            // On Windows, uv installs to %USERPROFILE%\.local\bin\uv.exe (default standalone)
            // or %USERPROFILE%\.cargo\bin\uv.exe (if installed via cargo).
            const winLocalPath = `${home}\\.local\\bin\\uv.exe`;
            const winCargoPath = `${home}\\.cargo\\bin\\uv.exe`;
            if (fs.existsSync(winLocalPath)) {
                return winLocalPath;
            }
            if (fs.existsSync(winCargoPath)) {
                return winCargoPath;
            }
            // Default to local path as most likely for standalone, even if not found
            return winLocalPath;
        }
        // On Unix-like systems, uv typically installs to ~/.local/bin/uv (standalone)
        // or ~/.cargo/bin/uv (if installed via cargo).
        const localBinPath = `${home}/.local/bin/uv`;
        const cargoBinPath = `${home}/.cargo/bin/uv`;
        if (fs.existsSync(localBinPath)) {
            return localBinPath;
        }
        if (fs.existsSync(cargoBinPath)) {
            return cargoBinPath;
        }
        // Default to localBinPath if neither found, as it's the most common for the install script.
        return localBinPath;
    }
    getUvToolPddPath() {
        const isWin = process.platform === 'win32';
        if (isWin) {
            // On Windows, uv installs tools to %LOCALAPPDATA%\uv\tools or %USERPROFILE%\.local\share\uv\tools
            const localAppData = process.env.LOCALAPPDATA || `${process.env.USERPROFILE}\\AppData\\Local`;
            return `${localAppData}\\uv\\tools\\pdd-cli\\Scripts\\pdd.exe`;
        }
        const home = process.env.HOME || '';
        return `${home}/.local/share/uv/tools/pdd-cli/bin/pdd`;
    }
    async runWithShellLogging(command, label) {
        console.log(`PDD: Running command${label ? ` [${label}]` : ''}: ${command}`);
        const res = await exec(command);
        if (res.stdout)
            console.log(`PDD: ${label || 'cmd'} stdout:\n${res.stdout}`);
        if (res.stderr)
            console.log(`PDD: ${label || 'cmd'} stderr:\n${res.stderr}`);
        return res;
    }
    async handleSuccessButtons(btn) {
        if (btn === 'Open Terminal') {
            vscode.commands.executeCommand('workbench.action.terminal.new');
        }
        else if (btn === 'Run Setup') {
            await this.runPddSetup();
        }
        else if (btn === 'View PDD Docs') {
            vscode.env.openExternal(vscode.Uri.parse('https://github.com/promptdriven/pdd#readme'));
        }
        else if (btn === 'View uv Docs') {
            vscode.env.openExternal(vscode.Uri.parse('https://docs.astral.sh/uv/'));
        }
    }
}
exports.PddInstaller = PddInstaller;
//# sourceMappingURL=pddInstaller.js.map