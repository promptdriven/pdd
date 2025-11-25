"use strict";
// src/extension.ts
// Main entry point for the VS Code extension integrating PDD (Prompt-Driven Development) CLI tooling.
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
exports.deactivate = exports.activate = void 0;
const vscode = __importStar(require("vscode"));
const pddInstaller_1 = require("./pddInstaller");
async function activate(context) {
    console.log('PDD VS Code extension activating...');
    const installer = new pddInstaller_1.PddInstaller(context);
    // Register commands synchronously; execute async logic inside handlers.
    // pdd.installCli: Triggers PDD CLI installation process
    const installDisposable = vscode.commands.registerCommand('pdd.installCli', async () => {
        try {
            await installer.installPddCli();
        }
        catch (err) {
            const message = err instanceof Error ? err.message : String(err);
            console.error('PDD: installCli failed:', message);
            vscode.window.showErrorMessage(`PDD: Installation failed. ${message}`);
        }
    });
    context.subscriptions.push(installDisposable);
    // pdd.checkCli: Checks if PDD CLI is installed and prompts user if not
    const checkDisposable = vscode.commands.registerCommand('pdd.checkCli', async () => {
        try {
            const installed = await installer.isPddCliInstalled();
            if (installed) {
                vscode.window.showInformationMessage('PDD CLI is already installed and ready to use!');
                return;
            }
            const selection = await vscode.window.showInformationMessage('PDD CLI is not installed. Would you like to install it now?', 'Install PDD CLI', 'Not Now');
            if (selection === 'Install PDD CLI') {
                await installer.installPddCli();
            }
        }
        catch (err) {
            const message = err instanceof Error ? err.message : String(err);
            console.error('PDD: checkCli failed:', message);
            vscode.window.showErrorMessage(`PDD: Check failed. ${message}`);
        }
    });
    context.subscriptions.push(checkDisposable);
    // pdd.runSetup: Executes the PDD setup process for API key configuration
    const setupDisposable = vscode.commands.registerCommand('pdd.runSetup', async () => {
        try {
            await installer.runPddSetup();
        }
        catch (err) {
            const message = err instanceof Error ? err.message : String(err);
            console.error('PDD: runSetup failed:', message);
            vscode.window.showErrorMessage(`PDD: Setup failed. ${message}`);
        }
    });
    context.subscriptions.push(setupDisposable);
    // pdd.upgradeToUv: Upgrades existing PDD installation to use uv package manager
    const upgradeDisposable = vscode.commands.registerCommand('pdd.upgradeToUv', async () => {
        try {
            await installer.upgradeToUvInstallation();
        }
        catch (err) {
            const message = err instanceof Error ? err.message : String(err);
            console.error('PDD: upgradeToUv failed:', message);
            vscode.window.showErrorMessage(`PDD: Upgrade to uv failed. ${message}`);
        }
    });
    context.subscriptions.push(upgradeDisposable);
    // Delay initial check to avoid interfering with VS Code startup
    setTimeout(() => {
        installer.checkAndPromptInstallation().catch((err) => {
            const message = err instanceof Error ? err.message : String(err);
            console.warn('PDD: Initial checkAndPromptInstallation encountered an issue:', message);
            // Silent by design; do not surface to user during startup.
        });
    }, 2000);
    console.log('PDD VS Code extension activated.');
}
exports.activate = activate;
function deactivate() {
    console.log('PDD VS Code extension deactivated.');
}
exports.deactivate = deactivate;
//# sourceMappingURL=extension.js.map