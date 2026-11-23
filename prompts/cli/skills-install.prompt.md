# Global PDD skill installation and automatic sync

Own `src/skills-install.mjs`. Export `PDD_SKILL_NAMES`, `RETIRED_SKILL_NAMES`, `hasClaudePluginInstall({home, claudeConfigDir})`, `setupSkills({packageRoot, cwd, home, claudeConfigDir, codexHome, skillsDir})`, `syncOwnedUserSkills({packageRoot, home, claudeConfigDir, codexHome, stateRoot, force, onError})`, and `findSkills({packageRoot, cwd, home, claudeConfigDir, codexHome})`.

## Domain decisions

- **Shipped and retired skills:**
  - `PDD_SKILL_NAMES`: `['pdd']` (the single `/pdd` router skill).
  - `RETIRED_SKILL_NAMES`: `['pdd-autopilot', 'pdd-check', 'pdd-merge', 'pdd-setup', 'pdd-prompting', 'pdd-small-change', 'pdd-bug', 'pdd-feature', 'pdd-product', 'pdd-graph']`. Setup and sync remove only `.pdd-skill.json`-marked real folders of retired skills in user skill roots; unmarked folders, symlinks, files, and project folders are never modified.
- **Laptop-wide global targets (`setupSkills`):**
  - Default targets:
    1. `Codex` (`<home>/.agents/skills`) — open agentskills.io standard (Codex, Gemini, Cursor, etc.).
    2. `Claude` (`<claudeConfigDir>/skills` when `claudeConfigDir` is absolute, else `<home>/.claude/skills`).
    3. `Antigravity` (`<home>/.gemini/config/skills`) — targeted **only** when Antigravity is detected (`<home>/.gemini/antigravity-cli`, `<home>/.gemini/config/mcp_config.json`, `agy` executable on `PATH`, or existing `.pdd-skill.json`-marked skills in `<home>/.gemini/config/skills`).
  - When `skillsDir` is provided, target only `[resolve(cwd, skillsDir)]` (`agent: 'Custom'`).
  - **Never skip global setup because `cwd` has project skills:** `setupSkills` reads only each target's own global root, never `<cwd>/.agents/skills` or `<cwd>/.claude/skills`.
  - **Plugin-aware Claude install & sync:** before writing into Claude's skills folder in both `setupSkills` and `syncOwnedUserSkills`, inspect `<claudeBase>/plugins/installed_plugins.json` (`<claudeConfigDir>` if absolute, else `<home>/.claude`). Match strictly PDD plugin IDs (`/^pdd(?:@|$)|^promptdriven\/pdd(?:@|$)/i`, never arbitrary plugins in a marketplace named `pdd`). When installed, STILL remove any `.pdd-skill.json`-marked `RETIRED_SKILL_NAMES` folders from Claude's skills folder (leaving unmarked folders, symlinks, and any existing `pdd` copy untouched) so stale split skills do not linger alongside the plugin, while skipping copying/syncing `PDD_SKILL_NAMES` (`setupSkills` returns `{agent: 'Claude', root, found: pluginPath, pluginManaged: true, removed, ...}`) to avoid duplicate `/pdd` entries.
  - Also refresh existing marker-owned secondary Codex user folders (`<home>/.codex/skills` and absolute `<codexHome>/skills`) without creating absent ones.
- **Marker ownership & atomic replacement:**
  - Marker file `.pdd-skill.json` holds `{"package":"pdd","version","digest"}` where `digest` is the SHA-256 of sorted relative paths and file bytes.
  - Replace only real directories with `.pdd-skill.json` whose version is older, whose same-version digest differs, or whose marker JSON is invalid. Never overwrite newer versions, unmarked folders, symlinks, or regular files.
  - Copy into a temporary sibling directory, write the marker, remove the old directory, and rename atomically.
- **Automatic once-per-version sync (`syncOwnedUserSkills`):**
  - Cache `<stateRoot>/skills-sync.json` (`{"version": VERSION}`, `stateRoot` defaults to `resolvePddStateBase` / `<home>/.local/state/pdd`).
  - When `!force` and `skills-sync.json` already matches `version`, return `{updated: []}` immediately with zero directory scans.
  - Inspect deduplicated user roots (`<home>/.agents/skills`, secondary Codex roots, Claude's user root, `<home>/.gemini/config/skills`) for existing marker-owned folders.
  - When zero marker-owned roots exist, write zero skill folders, record `skills-sync.json` for `version` (fail-open, preventing infinite rescans on subsequent CLI invocations), and return `{updated: []}`.
- **Read-only discovery (`findSkills`):**
  - Performs zero writes; checks project and user folders (canonicalized and deduplicated), tagging each returned row with `scope: 'project' | 'user'`, plus stale partial folders across `.agents/skills`, `.codex/skills`, `$CODEX_HOME/skills`, `.claude/skills`, and `.gemini/config/skills`.

## Dependencies

- Read the full [Prompting guide](../../skills/pdd/references/prompting.md) before changing this prompt.
- Follow the [public boundary](public-boundary.prompt.md).
