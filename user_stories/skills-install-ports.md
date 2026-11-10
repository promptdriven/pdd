# Find and install PDD skills for Codex and Claude through Runtime ports

I can discover installed PDD skills across project and user folders, classify stale copies, update older marker-owned copies, and install missing skills into the user folder through declared blob and filesystem ports.

```pdd-boundary
prompts/cli/skills-install.prompt.md
```

## Acceptance criteria

1. `setupSkills` updates an older `.pdd-skill.json`-marked skill in `.agents/skills` under `home`, recognizes `.agents/skills` under `cwd` when all ten skills exist there (reporting `stale: "older"` for an un-marked copy with an older `pdd-skills` version), installs a missing skill into `skills` under `claudeConfigDir` when `claudeConfigDir` is an absolute path, and fails with `missing_skills_package` when `package.json` under `packageRoot` is missing.
2. `findSkills` performs read-only discovery and stale classification without calling `fs.copySkill`, and fails with `missing_skills_package` when `package.json` under `packageRoot` is missing.
