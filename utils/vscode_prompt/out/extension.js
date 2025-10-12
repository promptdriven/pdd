"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.deactivate = exports.activate = void 0;
const vscode = require("vscode");
const pddInstaller_1 = require("./pddInstaller");
function activate(context) {
    console.log('PDD Extension is now active!');
    const installer = new pddInstaller_1.PddInstaller(context);
    // Register command to install PDD CLI
    const installCommand = vscode.commands.registerCommand('pdd.installCli', async () => {
        await installer.installPddCli();
    });
    // Register command to check if PDD CLI is installed
    const checkCommand = vscode.commands.registerCommand('pdd.checkCli', async () => {
        const isInstalled = await installer.isPddCliInstalled();
        if (isInstalled) {
            vscode.window.showInformationMessage('PDD CLI is already installed and ready to use!');
        }
        else {
            vscode.window.showInformationMessage('PDD CLI is not installed. Would you like to install it?', 'Install PDD CLI', 'Not Now').then(selection => {
                if (selection === 'Install PDD CLI') {
                    installer.installPddCli();
                }
            });
        }
    });
    // Register command to run PDD setup
    const setupCommand = vscode.commands.registerCommand('pdd.runSetup', async () => {
        await installer.runPddSetup();
    });
    // Register command to upgrade PDD to uv installation
    const upgradeCommand = vscode.commands.registerCommand('pdd.upgradeToUv', async () => {
        await installer.upgradeToUvInstallation();
    });
    context.subscriptions.push(installCommand, checkCommand, setupCommand, upgradeCommand);
    // Check on activation if PDD CLI is installed
    // Wait a bit to let VS Code finish startup
    setTimeout(async () => {
        await installer.checkAndPromptInstallation();
    }, 2000);
}
exports.activate = activate;
function deactivate() {
    console.log('PDD Extension is now deactivated.');
}
exports.deactivate = deactivate;
//# sourceMappingURL=extension.js.map