# Global PDD skill installation and automatic sync

Own `src/shared/skills-install.mjs` (re-exported via `src/skills-install.mjs`). Export `PDD_SKILL_NAMES`, `RETIRED_SKILL_NAMES`, `hasClaudePluginInstall({home, claudeConfigDir})`, `setupSkills({packageRoot, cwd, home, claudeConfigDir, codexHome, skillsDir, env})`, `syncOwnedUserSkills({packageRoot, home, claudeConfigDir, codexHome, stateRoot, env, force, onError})`, and `findSkills({packageRoot, cwd, home, claudeConfigDir, codexHome})`.

## Domain decisions

- **Shipped and retired skills:**
  - `PDD_SKILL_NAMES`: `['pdd']` (the single `/pdd` router skill).
  - `RETIRED_SKILL_NAMES`: `['pdd-autopilot', 'pdd-check', 'pdd-merge', 'pdd-setup', 'pdd-prompting', 'pdd-small-change', 'pdd-bug', 'pdd-feature', 'pdd-product', 'pdd-graph']`.
- **Safe PDD-managed skill recognition & strict safety invariants:**
  - A directory is **PDD-managed** iff it is a real directory (not a symlink or regular file), does not contain `.git`, and contains **either** a regular `.pdd-skill.json` marker file (any content, including invalid JSON) **or** a regular non-symlink `SKILL.md` file with `pdd-skills: <version>` in its YAML frontmatter (`skillVersion(dir) !== null`, supporting LF and CRLF).
  - **Auto-install / auto-upgrade `PDD_SKILL_NAMES` (`['pdd']`):** replace any PDD-managed directory (either `.pdd-skill.json`-marked or unmarked `pdd-skills:`-tagged) whose version is older, whose same-version digest differs, or whose `.pdd-skill.json` is invalid JSON, with a cleanly `.pdd-skill.json`-marked copy. Never downgrade newer versions; never overwrite a folder lacking both `.pdd-skill.json` and `pdd-skills:` frontmatter; never overwrite a symlink (such as a local developer git checkout symlink) or regular file.
  - **Auto-remove retired skills (`RETIRED_SKILL_NAMES`):**
    - Remove any real PDD-managed directory (`.pdd-skill.json` or `pdd-skills:` frontmatter, without `.git`) in `RETIRED_SKILL_NAMES`.
    - Unlink (via `unlinkSync` on the link itself — never following or deleting external targets) any symlink in `RETIRED_SKILL_NAMES` that does NOT point inside a git checkout (any ancestor below `$HOME` containing `.git`, checked for both live and dangling targets via `readlinkSync`) and is **either** dangling (`ENOENT`/`ENOTDIR`) **or** points to a live PDD-managed directory inside another known user agent skill directory (such as `~/.claude/skills/pdd-bug -> ../../.agents/skills/pdd-bug` created by `npx skills add`).
  - **Never touch:** non-PDD skills (e.g. `finish-pr`, `cot-review`), folders lacking both `.pdd-skill.json` and `pdd-skills:` frontmatter, symlinks pointing outside user agent skill roots or into developer git checkouts, or project-local skill folders.
- **Laptop-wide global targets (`setupSkills`):**
  - Default targets:
    1. `Codex` (`<home>/.agents/skills`) — open agentskills.io standard (Codex, Gemini, Cursor, etc.).
    2. `Claude` (`<claudeConfigDir>/skills` when `claudeConfigDir` is absolute, else `<home>/.claude/skills`).
    3. `Antigravity` (`<home>/.gemini/config/skills`) — targeted **only** when Antigravity is detected (`<home>/.gemini/antigravity-cli`, `<home>/.gemini/config/mcp_config.json`, `agy` executable on `PATH`, or existing PDD-managed skills or removable retired skills in `<home>/.gemini/config/skills`).
  - When `skillsDir` is provided, target only `[resolve(cwd, skillsDir)]` (`agent: 'Custom'`).
  - **Never skip global setup because `cwd` has project skills:** `setupSkills` reads only each target's own global root, never `<cwd>/.agents/skills` or `<cwd>/.claude/skills`.
  - **Plugin-aware Claude install & sync:** before writing into Claude's skills folder in both `setupSkills` and `syncOwnedUserSkills`, inspect `<claudeBase>/plugins/installed_plugins.json` (`<claudeConfigDir>` if absolute, else `<home>/.claude`). Match strictly PDD plugin IDs (`/^pdd(?:@|$)|^promptdriven\/pdd(?:@|$)/i`, never arbitrary plugins in a marketplace named `pdd`). When installed, STILL remove any removable `RETIRED_SKILL_NAMES` directories and retired agent-root/dangling symlinks from Claude's skills folder (leaving custom folders, external/git symlinks, and any existing `pdd` copy untouched) so stale split skills do not linger alongside the plugin, while skipping copying/syncing `PDD_SKILL_NAMES` (`setupSkills` returns `{agent: 'Claude', root, found: pluginPath, pluginManaged: true, removed, ...}`) to avoid duplicate `/pdd` entries.
  - Also refresh existing PDD-managed secondary Codex user folders (`<home>/.codex/skills` and absolute `<codexHome>/skills`) without creating absent ones.
- **Marker ownership & atomic replacement:**
  - Marker file `.pdd-skill.json` holds `{"package":"pdd","version","digest"}` where `digest` is the SHA-256 of sorted relative paths and file bytes.
  - Copy into a temporary sibling directory, write the marker, swap the old directory to a backup, rename atomically, and remove backup (rolling back best-effort on failure).
- **Automatic once-per-version sync (`syncOwnedUserSkills`):**
  - Cache `<stateRoot>/skills-sync.json` (`{"version": VERSION}`, `stateRoot` defaults to `resolvePddStateBase(env ?? { HOME: home })`).
  - When `!force` and `skills-sync.json` already matches `version`, return `{updated: []}` immediately with zero directory scans.
  - Inspect deduplicated user roots (`<home>/.agents/skills`, secondary Codex roots, Claude's user root, `<home>/.gemini/config/skills`) using the same PDD-managed directory and retired-symlink rules as `setupSkills`.
  - Never stamp `skills-sync.json` as current when any error occurred OR when any stranded retired PDD skill remains in the inspected user roots. When zero managed roots exist and zero retired PDD skills remain, write zero skill folders, record `skills-sync.json` for `version` (fail-open), and return `{updated: []}`.
- **Read-only discovery (`findSkills`):**
  - Performs zero writes; checks BOTH `PDD_SKILL_NAMES` and `RETIRED_SKILL_NAMES` across project and user folders (canonicalized and deduplicated), tagging each returned row with `scope: 'project' | 'user'`, `root`, `found`, `stale`, `staleSkills`, and `retiredSkills` (`[{name, kind: 'dir'|'symlink', version}]`).
  - Surfaces stranded retired PDD skills (`.pdd-skill.json`-marked, `pdd-skills:` frontmatter-marked, or retired agent-root/dangling symlinks) even when `pdd/` is missing (`found: null, root: folder, retiredSkills: [...]`) so `pdd --version` warns loudly whenever `pdd/` is missing/outdated or retired PDD skills remain.

## Dependencies

- Read the full [Prompting guide](../../skills/pdd/references/prompting.md) before changing this prompt.
- Follow the [public boundary](public-boundary.prompt.md).
