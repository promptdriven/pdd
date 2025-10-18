# Welcome to your VS Code Extension

## What's in the folder

* This folder contains all of the files necessary for your extension.
* `package.json` - this is the manifest file in which you declare your language support and define the location of the grammar file that has been copied into your extension.
* `syntaxes/prompt.tmLanguage.json` - this is the Text mate grammar file that is used for tokenization.
* `language-configuration.json` - this is the language configuration, defining the tokens that are used for comments and brackets.
* `src/extension.ts` - main extension entry point with command registration and activation logic.
* `src/pddInstaller.ts` - PDD CLI installation system with cross-platform support.

## Get up and running straight away

* Make sure the language configuration settings in `language-configuration.json` are accurate.
* Press `F5` to open a new window with your extension loaded.
* Create a new file with a `.prompt` extension to test syntax highlighting.
* The extension will automatically detect if PDD CLI is installed and offer installation if needed.
* Verify that syntax highlighting works and that the language configuration settings are working.

## Extension Features

### PDD CLI Integration
* **uv-Only Installation**: Simple, reliable installation using uv (the modern Python package manager)
* **Smart Detection**: Detects existing installations across uv tools and common paths
* **Automatic uv Setup**: Installs uv automatically if not present
* **Cross-Platform**: Works on macOS, Linux, and Windows
* **Command Palette Integration**: 
  - `PDD: Install PDD CLI` - Install PDD CLI using uv
  - `PDD: Check PDD CLI Installation` - Verify installation status
  - `PDD: Run PDD Setup` - Configure API keys and settings
  - `PDD: Upgrade PDD to uv Installation` - Ensure using latest uv-based installation

## Make changes

* You can relaunch the extension from the debug toolbar after making changes to the files listed above.
* You can also reload (`Ctrl+R` or `Cmd+R` on Mac) the VS Code window with your extension to load your changes.

## Add more language features

* To add features such as IntelliSense, hovers and validators check out the VS Code extenders documentation at https://code.visualstudio.com/docs

## Install your extension

* To start using your extension with Visual Studio Code copy it into the `<user home>/.vscode/extensions` folder and restart Code.
* To share your extension with the world, read on https://code.visualstudio.com/docs about publishing an extension.

## Package & Local Install (.vsix)

Build a distributable `.vsix` and install it locally for testing:

- Package (one-off): `npx @vscode/vsce package`
- Or with global install: `vsce package`

Output: `prompt-<version>.vsix` in the project folder (e.g., `prompt-0.0.1.vsix`).

Install locally:

- VS Code: `code --install-extension prompt-<version>.vsix`
- Cursor: `cursor --install-extension prompt-<version>.vsix`
- VSCodium: `codium --install-extension prompt-<version>.vsix`
- Kiro: Use the extension manager or CLI equivalent
- Windsurf: Use the extension manager or CLI equivalent
- Other OpenVSX-compatible IDEs: Use the extension manager or CLI equivalent

Tips:

- Bump `version` in `package.json` before packaging.
- Ensure `publisher` in `package.json` is correct.
- `.vscodeignore` controls what’s included in the package.
