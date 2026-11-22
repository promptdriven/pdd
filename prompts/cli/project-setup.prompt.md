# Project setup and per-repo initialization

Own `src/project-setup.mjs`. Export `PDD_BLOCK`, `detectProjectStack(root)`, `setupProject({cwd, packageRoot})` and `initProject({cwd, packageRoot})`.

`pdd init` opts a repository into PDD without editing `.gitignore` (`.pdd/.gitignore` is managed automatically whenever `.pdd/` is created) and without touching global laptop skills or MCP configs.

## Domain decisions

- **Canonical 4-line PDD block (`PDD_BLOCK`):** owned directly in `src/project-setup.mjs` (no external `pdd-setup` skill dependency):
  - Line 1: `<!-- pdd:start -->`
  - Line 2: tells agents to edit the owning `.prompt.md` before changing owned code and verify with `pdd status`, `pdd lint`, and `pdd test`
  - Line 3: names `/pdd` (Claude Code) and `$pdd` (Codex) with the bootstrap hint `npm i -g @promptdriven/pdd && pdd setup` for fork contributors
  - Line 4: `<!-- pdd:end -->`
  - Never include `pdd workflow run` or `RUNBOOK.md`.
- **Target file selection:** inside the target directory, choose `CLAUDE.md` when it already exists, else `AGENTS.md` (creating `AGENTS.md` with the block and a trailing newline when neither exists).
- **Safe marker replacement, CRLF preservation, and symlink refusal:**
  - Inspect the target file with `lstatSync` before reading or writing. Refuse symbolic links and non-regular files with an explicit 4-part error naming the path, the invariant violated, a 1-line fix, and the rerun command (`pdd init`).
  - Split lines on `/\r?\n/` so CRLF files never miss existing markers or append a duplicate block, and preserve the file's dominant line ending (`\r\n` when present, else `\n`).
  - If the file has no marker lines, append one blank line and `PDD_BLOCK`. If it has exactly one `<!-- pdd:start -->` followed by one `<!-- pdd:end -->`, replace that inclusive span in place while preserving all surrounding text. Any other marker count or order throws without writing.
  - If the resulting content equals the existing content byte-for-byte, write nothing and return `changed: false`. Otherwise write atomically via a temporary sibling file and rename, preserving existing permissions (`0o644` for new files).
- **Stack detection (`detectProjectStack(root)`):** read-only inspection of repository root manifests (`package.json`, `tsconfig.json`, lockfiles, `pyproject.toml`/`pytest.ini`, `go.mod`, `Cargo.toml`, `Gemfile`, `pom.xml`, `build.gradle*`) returning `{language, testCommand}` (`null` when unknown), ignoring npm's placeholder `"no test specified"` script.
- **`initProject({cwd, packageRoot})`:** resolve the canonical Git repository root via `resolveRepoRoot(cwd)` (falling back to `cwd` when outside Git), run `setupProject({cwd: root, packageRoot})`, run `detectProjectStack(root)`, and return `{root, inGit, file, changed, language, testCommand}`.

## Public contract

- `PDD_BLOCK`: string constant containing the 4-line marked block.
- `detectProjectStack(root) -> { language: string | null, testCommand: string | null }`
- `setupProject({ cwd, packageRoot }) -> { file: string, changed: boolean }`
- `initProject({ cwd, packageRoot }) -> Promise<{ root: string, inGit: boolean, file: string, changed: boolean, language: string | null, testCommand: string | null }>`

## Dependencies

- Read the full [Prompting guide](../../skills/pdd/references/prompting.md) before changing this prompt.
- Follow the [public boundary](public-boundary.prompt.md).
- Layer-0 `src/shared/git-context.mjs` (`resolveRepoRoot`) and `src/shared/atomic-fs.mjs`.
