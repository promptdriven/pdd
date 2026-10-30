# Find or install the PDD skills for each agent

Own `src/skills-install.mjs`. Export `PDD_SKILL_NAMES` (`pdd-prompting`, `pdd-setup`, `pdd-small-change`, `pdd-bug`, `pdd-feature`, `pdd-product`), `setupSkills({packageRoot, cwd, home, claudeConfigDir})` and `findSkills` (same arguments). Only [pdd setup](pdd-cli.prompt.md) calls `setupSkills`. No other command writes skills. `pdd --version` calls `findSkills`: it does step 2 and the stale check below with no writes, and returns `{agent, found, stale}` for each agent, Codex first.

The PDD skills ship in `<packageRoot>/skills/<name>/`. People often install them with `npx skills add`, which copies or symlinks them into the project or the user folder. pdd setup must not add a second copy then. It copies the skills only when an agent cannot find them.

## Where each agent reads skills

| Agent | Read folders, in order | User folder (where pdd installs) |
| --- | --- | --- |
| Codex | `<cwd>/.agents/skills`, `<home>/.agents/skills` | `<home>/.agents/skills` |
| Claude | `<cwd>/.claude/skills`, then its user folder | `<claudeConfigDir>/skills` when `claudeConfigDir` is an absolute path, else `<home>/.claude/skills` |

Claude started with `CLAUDE_CONFIG_DIR` reads `<CLAUDE_CONFIG_DIR>/skills` and not `<home>/.claude/skills` (checked with `claude -p`), so a copy in `~/.claude/skills` does not count then.

## What setupSkills does, for each agent

1. Update: in the user folder, replace each PDD skill folder that carries the pdd marker and is older or changed (see the table below).
2. Find: the first read folder where all six `<folder>/<name>/SKILL.md` files exist. A symlinked skill folder counts.
3. If no read folder has all six skills, copy each skill that is missing from the user folder.

Return one result per agent, Codex first: `{agent, root, found, stale, installed, updated}`. `root` is the user folder, `found` is the found read folder or null, and `installed` and `updated` are the absolute folders that were copied. `stale` says how the found skills compare with the package (0.1.6 tester: setup said "found" for npx skills copies older than pdd): `'older'` when every found skill that is not current is older: a pdd marker with an older version, or (without a marker) files that are not the package's and a version line that is older or missing. `'differs'` when one differs in another way (a folder without a marker whose files, hashed like the digest, are not the package's and whose version line is the package version; a marker of the same version with another digest; a marker that is not valid JSON), else null (the same files, a newer marker or version line, or unreadable). Compare the files first, so a version line that a release forgot to change never warns about current files. setupSkills never changes a found folder that it does not own. A failure in one agent does not stop the other: put `error` in that agent's result instead of throwing. It never writes into the person's repo.

## The version line

Each packaged `SKILL.md` names its version in its frontmatter, under `metadata:` (the Agent Skills field for extra keys, so Codex and Claude Code still load the skill): `  pdd-skills: VERSION`, the package version. A person or an agent can read it in the installed copy. Copies from before 0.1.9 have no such line, so a missing line counts as older. Read it with a line match inside the frontmatter; any read error means no line.

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
