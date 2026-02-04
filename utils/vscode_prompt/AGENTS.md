# Repository Guidelines

## Project Structure & Module Organization
- `package.json`: VS Code extension manifest (language id `prompt`) with PDD CLI integration commands.
- `language-configuration.json`: Brackets, comments, and editor behaviors for `.prompt` files.
- `syntaxes/prompt.tmLanguage.json`: TextMate grammar for `.prompt` files.
- `prompts/prompt.tmLanguage_json.prompt`: Source asset/example used for grammar work.
- `src/extension.ts`: Main extension entry point with command registration for PDD CLI features.
- `src/pddInstaller.ts`: Smart PDD CLI installation and detection system with uv-first logic.
- Docs: `README.md`, `CHANGELOG.md`, `LICENSE.md`, `vsc-extension-quickstart.md`.

## Build, Test, and Development Commands
- Run locally: open in VS Code and use "Run Extension" (F5) to launch an Extension Development Host.
- Package: `npm install -g @vscode/vsce` then `vsce package` to create a `.vsix`.
- Publish (maintainers): `vsce publish` with the configured `publisher` in `package.json`.
- Lint/format: none configured; see Style section before adding tools.
- Test PDD CLI integration: use the "PDD: Install CLI" command in the Extension Development Host.
- Debug installation: check VS Code Developer Console for detailed logging from pddInstaller.ts.

## Coding Style & Naming Conventions
- JSON: 2-space indentation, UTF-8, no trailing commas.
- TypeScript: Standard TypeScript conventions, async/await for promises, clear function names.
- Filenames: lowercase, hyphenated where needed (e.g., `my-asset.json`).
- Grammar: keep scope names consistent; place grammars under `syntaxes/` and configs at repo root.
- Language id and extension remain `prompt` / `.prompt` unless a breaking change is planned.

## Testing Guidelines
- Manual checks: open a `.prompt` file in the Extension Development Host and use “Developer: Inspect Editor Tokens and Scopes”.
- Scenarios: verify keywords, strings, comments, and edge cases render as expected.
- Optional tooling (future): `vscode-tmgrammar-test` for snapshot-based grammar tests. Keep sample files under `test-fixtures/` if added.

## Commit & Pull Request Guidelines
- Commits: present-tense, imperative (“Add…”, “Fix…”). Use short scope prefixes when helpful (e.g., `grammar:`, `docs:`, `chore:`). Keep subjects ≤72 chars.
- PRs: include summary, motivation, before/after screenshots or GIFs for highlighting changes, and link related issues.
- Changelog: update `CHANGELOG.md` for user-visible changes; bump version in `package.json` when publishing.

## Security & Configuration Tips
- Keep `engines.vscode` accurate; test against that VS Code version.
- No runtime code here; validate JSON with a linter or VS Code JSON schema hints before committing.
