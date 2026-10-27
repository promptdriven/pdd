# Find or install the PDD skills for each agent

Own `src/skills-install.mjs`. Export `PDD_SKILL_NAMES` (`pdd-prompting`, `pdd-setup`, `pdd-small-change`, `pdd-bug`, `pdd-feature`) and `setupSkills({packageRoot, cwd, home, claudeConfigDir})`. Only [pdd setup](pdd-cli.prompt.md) calls it. No other command writes skills.

The PDD skills ship in `<packageRoot>/skills/<name>/`. People often install them with `npx skills add`, which copies or symlinks them into the project or the user folder. pdd setup must not add a second copy then. It copies the skills only when an agent cannot find them.

## Where each agent reads skills

| Agent | Read folders, in order | User folder (where pdd installs) |
| --- | --- | --- |
| Codex | `<cwd>/.agents/skills`, `<home>/.agents/skills` | `<home>/.agents/skills` |
| Claude | `<cwd>/.claude/skills`, then its user folder | `<claudeConfigDir>/skills` when `claudeConfigDir` is an absolute path, else `<home>/.claude/skills` |

Claude started with `CLAUDE_CONFIG_DIR` reads `<CLAUDE_CONFIG_DIR>/skills` and not `<home>/.claude/skills` (checked with `claude -p`), so a copy in `~/.claude/skills` does not count then.

## What setupSkills does, for each agent

1. Update: in the user folder, replace each PDD skill folder that carries the pdd marker and is older or changed (see the table below).
2. Find: the first read folder where all five `<folder>/<name>/SKILL.md` files exist. A symlinked skill folder counts.
3. If no read folder has all five skills, copy each skill that is missing from the user folder.

Return one result per agent, Codex first: `{agent, root, found, installed, updated}`. `root` is the user folder, `found` is the found read folder or null, and `installed` and `updated` are the absolute folders that were copied. A failure in one agent does not stop the other: put `error` in that agent's result instead of throwing. It never writes into the person's repo.

## The marker

Each folder that pdd copies holds a marker file `.pdd-skill.json`: `{"package":"pdd","version","digest"}`. `version` is the package version from `<packageRoot>/package.json`. `digest` is the sha256 of the skill's packaged files: each relative path (sorted, `/` separators) and its bytes.

| Folder in the user folder | Action |
| --- | --- |
| Missing | Copy, but only in step 3. |
| Has a marker with an older version | Replace. |
| Has a marker with the same version and another digest | Replace. A new build of the same version must reach the person. |
| Has a marker with the same version and digest | Keep. Do no writes. |
| Has a marker with a newer version | Keep. Never downgrade. |
| Has a marker that is not valid JSON | Replace. The marker name shows that pdd owns it. |
| Has no marker, or is a symlink or a file | Keep. It belongs to the person or to another installer. |

Compare versions by their numeric `major.minor.patch` parts.

## How to copy

Replace the whole folder, so files that a new version removed do not stay. Copy the package folder to a temporary sibling folder, write the marker into it, remove the old folder, then rename the temporary folder into place. Create the user folder when it is missing. Never follow a symlink when you remove a folder. Read the package files and compute the digests before any write.

## Dependencies

Read the full [Prompting guide](../../docs/prompting-guide.md) before you change this prompt. Follow the [alpha boundary](public-boundary.prompt.md).
