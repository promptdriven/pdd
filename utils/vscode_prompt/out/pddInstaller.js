"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.PddInstaller = void 0;
const vscode = require("vscode");
const cp = require("child_process");
const util_1 = require("util");
const exec = (0, util_1.promisify)(cp.exec);
class PddInstaller {
    constructor(context) {
        this.context = context;
    }
    async isPddCliInstalled() {
        try {
            // First try the standard PATH
            await exec('pdd --version');
            return true;
        }
        catch {
            // If that fails, try uv tool path (if uv is available)
            try {
                // Check uv tools directory
                const uvToolPath = `${process.env.HOME}/.local/share/uv/tools/pdd-cli/bin/pdd`;
                await exec(`${uvToolPath} --version`);
                return true;
            }
            catch {
                // Try uv tool run command
                try {
                    await exec('uv tool run pdd-cli --version');
                    return true;
                }
                catch {
                    // Try conda environment if it exists
                    try {
                        await exec('conda run -n pdd pdd --version');
                        return true;
                    }
                    catch {
                        // Try common installation paths as fallback
                        const commonPaths = [
                            '/opt/anaconda3/envs/pdd/bin/pdd',
                            '/opt/miniconda3/envs/pdd/bin/pdd',
                            `${process.env.HOME}/.local/bin/pdd`,
                            `${process.env.HOME}/anaconda3/envs/pdd/bin/pdd`,
                            `${process.env.HOME}/miniconda3/envs/pdd/bin/pdd`,
                            '/opt/anaconda3/bin/pdd',
                            '/opt/miniconda3/bin/pdd',
                            `${process.env.HOME}/anaconda3/bin/pdd`,
                            `${process.env.HOME}/miniconda3/bin/pdd`,
                        ];
                        for (const path of commonPaths) {
                            try {
                                await exec(`${path} --version`);
                                return true;
                            }
                            catch {
                                continue;
                            }
                        }
                        return false;
                    }
                }
            }
        }
    }
    async installPddCli() {
        try {
            console.log('PDD: Starting installation process...');
            // First ask user how they want to install PDD
            const choice = await vscode.window.showInformationMessage('How would you like to install PDD CLI?', {
                modal: false,
                detail: 'uv provides the latest version and best experience. pip is a reliable fallback option.'
            }, 'Install with uv (recommended)', 'Install with pip', 'Cancel');
            if (!choice || choice === 'Cancel') {
                vscode.window.showInformationMessage('PDD CLI installation was cancelled.');
                return;
            }
            // Check if conda is available and if pdd environment exists
            const installMethod = await this.detectInstallationMethod();
            console.log('PDD: Selected installation method:', installMethod.type);
            // Show progress notification
            const installationMethod = await vscode.window.withProgress({
                location: vscode.ProgressLocation.Notification,
                title: "Installing PDD CLI",
                cancellable: false
            }, async (progress) => {
                progress.report({ increment: 0, message: "Installing PDD CLI..." });
                let installCmd;
                let installationMethod = 'fallback';
                if (choice === 'Install with uv (recommended)') {
                    // User specifically chose uv
                    try {
                        await exec('uv --version');
                        console.log('PDD: uv is available, using for installation');
                        installCmd = `uv tool install pdd-cli`;
                        installationMethod = 'uv';
                    }
                    catch {
                        console.log('PDD: uv not found, installing uv first');
                        progress.report({ increment: 10, message: "Installing uv package manager..." });
                        // Install uv using the official installer
                        const uvInstallCmd = process.platform === 'win32'
                            ? 'powershell -c "irm https://astral.sh/uv/install.ps1 | iex"'
                            : 'curl -LsSf https://astral.sh/uv/install.sh | sh';
                        try {
                            console.log('PDD: Installing uv with command:', uvInstallCmd);
                            await exec(uvInstallCmd);
                            progress.report({ increment: 15, message: "uv installed! Now installing PDD CLI..." });
                            // Since uv may have been added to PATH, we need to ensure it's available
                            const uvPath = process.platform === 'win32'
                                ? '%USERPROFILE%\\.cargo\\bin\\uv'
                                : '$HOME/.cargo/bin/uv';
                            // Try regular uv command first, then full path
                            try {
                                installCmd = `uv tool install pdd-cli`;
                                await exec('uv --version'); // Test if uv is in PATH
                                installationMethod = 'uv-installed';
                            }
                            catch {
                                console.log('PDD: uv not in PATH, using full path');
                                installCmd = `${uvPath} tool install pdd-cli`;
                                installationMethod = 'uv-installed';
                            }
                        }
                        catch (uvError) {
                            console.error('PDD: Failed to install uv:', uvError);
                            progress.report({ increment: 0, message: "uv installation failed, trying pip..." });
                            vscode.window.showErrorMessage('Failed to install uv. Falling back to pip installation.');
                            installCmd = await this.getFallbackInstallCommand();
                            installationMethod = 'fallback';
                        }
                    }
                }
                else {
                    // User chose pip installation
                    console.log('PDD: User chose pip installation');
                    progress.report({ increment: 0, message: "Installing PDD CLI with pip..." });
                    installCmd = await this.getFallbackInstallCommand();
                    installationMethod = 'fallback';
                }
                console.log('PDD: Executing install command:', installCmd);
                progress.report({ increment: 25, message: "Installing PDD CLI package..." });
                try {
                    const result = await exec(installCmd);
                    console.log('PDD: Installation command output:', result.stdout);
                    if (result.stderr) {
                        console.log('PDD: Installation command stderr:', result.stderr);
                    }
                }
                catch (installError) {
                    console.error('PDD: Installation command failed:', installError);
                    throw installError;
                }
                progress.report({ increment: 100, message: "PDD CLI installed successfully!" });
                // Return the installation method for the success message
                return installationMethod;
            });
            // Show appropriate success message based on installation method
            if (installationMethod === 'uv') {
                vscode.window.showInformationMessage('PDD CLI has been installed successfully using uv (the recommended package manager)! Run "pdd setup" in your terminal or use the "PDD: Run PDD Setup" command to configure API keys and install tab completion.', 'Open Terminal', 'Run Setup', 'View PDD Docs', 'View uv Docs').then(selection => {
                    if (selection === 'Open Terminal') {
                        vscode.commands.executeCommand('workbench.action.terminal.new');
                    }
                    else if (selection === 'Run Setup') {
                        this.runPddSetup();
                    }
                    else if (selection === 'View PDD Docs') {
                        vscode.env.openExternal(vscode.Uri.parse('https://github.com/promptdriven/pdd#readme'));
                    }
                    else if (selection === 'View uv Docs') {
                        vscode.env.openExternal(vscode.Uri.parse('https://docs.astral.sh/uv/'));
                    }
                });
            }
            else if (installationMethod === 'uv-installed') {
                vscode.window.showInformationMessage('PDD CLI has been installed successfully! We also installed uv (the recommended Python package manager) for future use. Run "pdd setup" in your terminal or use the "PDD: Run PDD Setup" command to configure API keys and install tab completion.', 'Open Terminal', 'Run Setup', 'View PDD Docs', 'View uv Docs').then(selection => {
                    if (selection === 'Open Terminal') {
                        vscode.commands.executeCommand('workbench.action.terminal.new');
                    }
                    else if (selection === 'Run Setup') {
                        this.runPddSetup();
                    }
                    else if (selection === 'View PDD Docs') {
                        vscode.env.openExternal(vscode.Uri.parse('https://github.com/promptdriven/pdd#readme'));
                    }
                    else if (selection === 'View uv Docs') {
                        vscode.env.openExternal(vscode.Uri.parse('https://docs.astral.sh/uv/'));
                    }
                });
            }
            else {
                vscode.window.showInformationMessage('PDD CLI has been installed using pip. Note: This may be an older version. For the latest features, consider installing uv and reinstalling with "uv tool install pdd-cli". Run "pdd setup" in your terminal or use the "PDD: Run PDD Setup" command to configure API keys.', 'Open Terminal', 'Run Setup', 'View PDD Docs', 'Install uv').then(selection => {
                    if (selection === 'Open Terminal') {
                        vscode.commands.executeCommand('workbench.action.terminal.new');
                    }
                    else if (selection === 'Run Setup') {
                        this.runPddSetup();
                    }
                    else if (selection === 'View PDD Docs') {
                        vscode.env.openExternal(vscode.Uri.parse('https://github.com/promptdriven/pdd#readme'));
                    }
                    else if (selection === 'Install uv') {
                        vscode.env.openExternal(vscode.Uri.parse('https://docs.astral.sh/uv/getting-started/installation/'));
                    }
                });
            }
        }
        catch (error) {
            console.error('Failed to install PDD CLI:', error);
            vscode.window.showErrorMessage(`Failed to install PDD CLI: ${error instanceof Error ? error.message : 'Unknown error'}. Please install manually via: uv tool install pdd-cli (recommended) or pip install pdd-cli`);
        }
    }
    async runPddSetup() {
        try {
            const terminal = vscode.window.createTerminal('PDD Setup');
            terminal.show();
            // Check if we should use conda environment
            try {
                await exec('conda env list | grep -q " pdd "');
                terminal.sendText('conda activate pdd && pdd setup && echo "Setup complete! Please reload your shell: source ~/.zshrc (or ~/.bashrc)"');
                vscode.window.showInformationMessage('PDD setup is running in the terminal with conda environment activated. Follow the prompts to configure your API keys, then reload your shell.', 'OK');
            }
            catch {
                // Check if uv installation exists
                const uvToolPath = `${process.env.HOME}/.local/share/uv/tools/pdd-cli/bin/pdd`;
                try {
                    await exec(`${uvToolPath} --version`);
                    // Use the full path for uv-installed PDD
                    terminal.sendText(`${uvToolPath} setup && echo "Setup complete! Please reload your shell: source ~/.zshrc (or ~/.bashrc)"`);
                }
                catch {
                    // Try uv tool run command
                    try {
                        await exec('uv tool run pdd-cli --version');
                        terminal.sendText('uv tool run pdd-cli setup && echo "Setup complete! Please reload your shell: source ~/.zshrc (or ~/.bashrc)"');
                    }
                    catch {
                        // Regular pdd command
                        terminal.sendText('pdd setup && echo "Setup complete! Please reload your shell: source ~/.zshrc (or ~/.bashrc)"');
                    }
                }
                vscode.window.showInformationMessage('PDD setup is running in the terminal. Follow the prompts to configure your API keys, then reload your shell for tab completion.', 'OK');
            }
        }
        catch (error) {
            console.error('Failed to run PDD setup:', error);
            vscode.window.showErrorMessage(`Failed to run PDD setup: ${error instanceof Error ? error.message : 'Unknown error'}`);
        }
    }
    async getFallbackInstallCommand() {
        // Try conda environment first if available
        try {
            await exec('conda --version');
            // Check if pdd environment already exists
            try {
                const { stdout } = await exec('conda env list');
                if (stdout.includes(' pdd ') || stdout.includes('\tpdd\t') || stdout.includes(' pdd\t') || stdout.includes('\tpdd ')) {
                    return 'conda run -n pdd pip install pdd-cli';
                }
            }
            catch {
                // Failed to list environments, continue to pip fallback
            }
        }
        catch {
            // Conda not available, continue to pip
        }
        // Fall back to pip with detected Python
        const pythonCmd = await this.detectPythonCommand();
        return `${pythonCmd} -m pip install --force-reinstall pdd-cli`;
    }
    async upgradeToUvInstallation() {
        try {
            // Check if PDD is already installed
            const isInstalled = await this.isPddCliInstalled();
            if (!isInstalled) {
                vscode.window.showWarningMessage('PDD CLI is not installed. Use "PDD: Install PDD CLI" command instead.');
                return;
            }
            // Check if uv is available
            try {
                await exec('uv --version');
                // uv is available, check if PDD is already installed via uv
                try {
                    await exec('uv tool list | grep pdd-cli');
                    vscode.window.showInformationMessage('PDD CLI is already installed via uv!');
                    return;
                }
                catch {
                    // PDD not installed via uv, offer to upgrade
                }
            }
            catch {
                // uv not available, ask to install it first
                const choice = await vscode.window.showInformationMessage('To upgrade to uv installation, we first need to install uv (the modern Python package manager). This will give you access to the latest PDD CLI features and faster updates.', 'Install uv and upgrade', 'Cancel');
                if (choice !== 'Install uv and upgrade') {
                    return;
                }
            }
            // Ask user if they want to upgrade
            const upgradeChoice = await vscode.window.showInformationMessage('Upgrade PDD CLI to uv installation?\n\n' +
                '✅ Benefits:\n' +
                '• Latest PDD CLI version\n' +
                '• Faster updates\n' +
                '• Better dependency management\n' +
                '• Isolated installation\n\n' +
                '⚠️ Your current PDD installation will be removed and reinstalled via uv.', {
                modal: true
            }, 'Yes, upgrade to uv', 'No, keep current installation');
            if (upgradeChoice === 'Yes, upgrade to uv') {
                await vscode.window.withProgress({
                    location: vscode.ProgressLocation.Notification,
                    title: "Upgrading PDD CLI to uv",
                    cancellable: false
                }, async (progress) => {
                    // First install uv if needed
                    try {
                        await exec('uv --version');
                        progress.report({ increment: 20, message: "uv is available" });
                    }
                    catch {
                        progress.report({ increment: 0, message: "Installing uv..." });
                        const uvInstallCmd = process.platform === 'win32'
                            ? 'powershell -c "irm https://astral.sh/uv/install.ps1 | iex"'
                            : 'curl -LsSf https://astral.sh/uv/install.sh | sh';
                        await exec(uvInstallCmd);
                        progress.report({ increment: 20, message: "uv installed!" });
                    }
                    // Remove current PDD installation (try different methods)
                    progress.report({ increment: 20, message: "Removing old PDD installation..." });
                    try {
                        await exec('pip uninstall pdd-cli -y');
                    }
                    catch {
                        // Try conda if pip fails
                        try {
                            await exec('conda remove pdd-cli -y');
                        }
                        catch {
                            // Ignore errors, might not be installed via these methods
                        }
                    }
                    // Install via uv
                    progress.report({ increment: 30, message: "Installing PDD CLI via uv..." });
                    const uvPath = process.platform === 'win32'
                        ? '%USERPROFILE%\\.cargo\\bin\\uv'
                        : '$HOME/.cargo/bin/uv';
                    try {
                        await exec('uv tool install pdd-cli');
                    }
                    catch {
                        // Try with full path
                        await exec(`${uvPath} tool install pdd-cli`);
                    }
                    progress.report({ increment: 10, message: "Upgrade complete!" });
                });
                vscode.window.showInformationMessage('PDD CLI has been successfully upgraded to uv installation! You now have access to the latest features and faster updates.', 'View uv Docs', 'OK').then(selection => {
                    if (selection === 'View uv Docs') {
                        vscode.env.openExternal(vscode.Uri.parse('https://docs.astral.sh/uv/'));
                    }
                });
            }
        }
        catch (error) {
            console.error('Failed to upgrade PDD CLI to uv:', error);
            vscode.window.showErrorMessage(`Failed to upgrade PDD CLI to uv: ${error instanceof Error ? error.message : 'Unknown error'}`);
        }
    }
    async detectInstallationMethod() {
        // Always prioritize uv as the primary installation method (PDD's official recommendation)
        try {
            await exec('uv --version');
            return { type: 'uv' };
        }
        catch {
            // uv not available, we'll install it first
            console.log('PDD: uv not found, will install uv first then use it for PDD installation');
            return { type: 'uv' }; // We'll handle uv installation in the main install method
        }
    }
    async detectPythonCommand() {
        // Try different Python commands in order of preference
        const commands = process.platform === 'win32'
            ? ['python', 'python3', 'py']
            : ['python3', 'python'];
        for (const cmd of commands) {
            try {
                const { stdout } = await exec(`${cmd} --version`);
                // Check if it's Python 3.7+
                const versionMatch = stdout.match(/Python (\d+)\.(\d+)/);
                if (versionMatch) {
                    const major = parseInt(versionMatch[1]);
                    const minor = parseInt(versionMatch[2]);
                    if (major >= 3 && (major > 3 || minor >= 7)) {
                        return cmd;
                    }
                }
            }
            catch {
                continue;
            }
        }
        throw new Error('No compatible Python installation found. Please install Python 3.7+ and try again.');
    }
    async checkAndPromptInstallation() {
        try {
            // Check if we should prompt for installation
            const config = vscode.workspace.getConfiguration('pdd');
            const shouldPrompt = config.get('promptForInstallation', true);
            console.log('PDD: Checking installation status...');
            if (!shouldPrompt) {
                console.log('PDD: Prompt for installation is disabled');
                return;
            }
            const isInstalled = await this.isPddCliInstalled();
            console.log('PDD: Is PDD CLI installed?', isInstalled);
            if (!isInstalled) {
                const action = await vscode.window.showInformationMessage('PDD CLI is not installed. Would you like to install it automatically?', 'Install PDD CLI', 'Not Now', 'Don\'t Ask Again');
                if (action === 'Install PDD CLI') {
                    await this.installPddCli();
                }
                else if (action === 'Don\'t Ask Again') {
                    // Store preference to not ask again
                    await config.update('promptForInstallation', false, vscode.ConfigurationTarget.Global);
                }
            }
        }
        catch (error) {
            console.error('PDD: Error during installation check:', error);
            // Don't show error to user for auto-check, just log it
        }
    }
}
exports.PddInstaller = PddInstaller;
//# sourceMappingURL=pddInstaller.js.map