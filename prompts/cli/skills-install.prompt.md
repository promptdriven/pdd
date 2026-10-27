# Install the PDD skills in the home folder

Own `src/skills-install.mjs`. Export `PDD_SKILL_NAMES` (`pdd-prompting`, `pdd-small-change`, `pdd-bug`, `pdd-feature`) and `installSkills({packageRoot, home})`.

The four skills ship in `<packageRoot>/skills/<name>/`. Codex finds personal skills in `<home>/.agents/skills/`. Claude finds them in `<home>/.claude/skills/`. `installSkills` keeps one copy of each skill in both folders, so the person's agent finds them in any chat. It never writes into the person's repo or the current folder.

## When to copy

Each installed skill folder holds a marker file `.pdd-skill.json`: `{"package":"pdd","version","digest"}`. `version` is the package version from `<packageRoot>/package.json`. `digest` is the sha256 of the skill's packaged files: each relative path (sorted, `/` separators) and its bytes.

| Installed folder | Action |
| --- | --- |
| Missing | Copy. |
| Has a marker with an older version | Replace. |
| Has a marker with the same version and another digest | Replace. A new build of the same version must reach the person. |
| Has a marker with the same version and digest | Keep. Do no writes. |
| Has a marker with a newer version | Keep. Never downgrade. |
| Has a marker that is not valid JSON | Replace. The marker name shows that pdd owns it. |
| Has no marker, or is a symlink or a file | Keep. It belongs to the person. |

Compare versions by their numeric `major.minor.patch` parts.

## How to copy

Replace the whole folder, so files that a new version removed do not stay. Copy the package folder to a temporary sibling folder, write the marker into it, remove the old folder, then rename the temporary folder into place. Create the skills root folders when they are missing. Never follow a symlink when you remove a folder.

Read the package files and compute the digests before any write. Handle each skills root on its own: a failure in one root does not stop the other. After both roots, throw the first error. The caller decides how to report it. Return `{installed, kept}`: the absolute folders that were copied and those that were kept.

## Dependencies

Read the full [Prompting guide](../../docs/prompting-guide.md) before you change this prompt. Follow the [alpha boundary](public-boundary.prompt.md). The [executable entry](bin-entry.prompt.md) calls `installSkills` before each command.
