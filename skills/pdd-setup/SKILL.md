---
name: pdd-setup
description: Set up a repo for PDD. Use when the person asks to set up PDD, add PDD to a project, or connect the PDD skills to this repo. Adds one short PDD block to CLAUDE.md or AGENTS.md.
metadata:
  pdd-skills: 0.1.11
---

# PDD setup

Add one short PDD block to the file that this repo's agents read. This skill only writes the block: if you can read it, the PDD skills are already installed. The `pdd setup` command writes the same block and also installs the skills when they are missing.

1. Pick the file: `CLAUDE.md` if it exists, else `AGENTS.md`. If neither exists, create `AGENTS.md`. Use the repo root.
2. Write this block exactly. Leave out the RUNBOOK.md line if the pdd-prompting skill has no RUNBOOK.md.
3. If the file already has a `<!-- pdd:start -->` … `<!-- pdd:end -->` block, replace only that block. Otherwise add the block at the end, after one empty line. Keep all other text.
4. If the block is already the same, change nothing. If only one marker is there, stop and ask the person.

```markdown
<!-- pdd:start -->
## PDD
This project uses PDD: prompts are the source. Write the prompt, Story and test cases first, then the code.
Skills: pdd-prompting (the Prompting guide), pdd-feature, pdd-bug, pdd-small-change. Call one with `$pdd-feature` in Codex or `/pdd-feature` in Claude Code, or just ask for it by name.
Full run with PRs: `pdd workflow start NAME ISSUE` (NAME: feature, bug or small-change).
Before you write prompts or tests, read RUNBOOK.md in the pdd-prompting skill.
<!-- pdd:end -->
```

Never paste the guide or a workflow into the file. Show the person the diff.
