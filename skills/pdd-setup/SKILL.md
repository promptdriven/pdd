---
name: pdd-setup
description: Set up a repo for PDD. Use when the person asks to set up PDD, add PDD to a project, or connect the PDD skills to this repo. Adds one short PDD block to CLAUDE.md or AGENTS.md.
metadata:
  pdd-skills: 0.1.27
---

# PDD setup

Add one short PDD block to the file that this repo's agents read, and keep `.pdd/` out of Git. This skill installs nothing: if you can read it, the PDD skills are already installed. The `pdd setup` command checks for a ready agent, does the same in the current folder, installs missing skills and updates eligible marked copies, then previews MCP changes for approval.

The bundled skills also include pdd-product, pdd-autopilot, pdd-check, pdd-merge, pdd-graph and pdd-setup. Bundled workflow names also include `product`.

1. Pick the file: `CLAUDE.md` if it exists, else `AGENTS.md`. If neither exists, create `AGENTS.md`. Use the repo root.
2. Write this block exactly. Leave out the RUNBOOK.md line if the pdd-prompting skill has no RUNBOOK.md.
3. If the file already has a `<!-- pdd:start -->` … `<!-- pdd:end -->` block, replace only that block. Otherwise add the block at the end, after one empty line. Keep all other text.
4. If the block is already the same, change nothing. If only one marker is there, stop and ask the person.
5. In a Git repo, add the line `.pdd/` at the end of the root `.gitignore` if no line there is `.pdd`, `.pdd/`, `/.pdd` or `/.pdd/` (no space at the start). Create the file if needed. Keep all other bytes. If the last such line starts with `!`, or there is no such line but a line starts with `!.pdd` or `!/.pdd` (for example `!.pdd/config.json`), change nothing and tell the person. `pdd test` keeps its local cache in `.pdd/`.

```markdown
<!-- pdd:start -->
## PDD
This project uses PDD. Change the prompt that owns a file before the file. New code starts with its prompt. Files that no prompt owns change directly, with a test when behavior changes.
Skills: pdd-prompting (the Prompting guide), pdd-feature, pdd-bug, pdd-small-change. Call one with `$pdd-feature` in Codex or `/pdd-feature` in Claude Code, or just ask for it by name.
Full run with PRs: `pdd workflow run NAME ISSUE` (NAME: feature, bug or small-change).
Before you write prompts or tests, read RUNBOOK.md in the pdd-prompting skill.
<!-- pdd:end -->
```

Never paste the guide or a workflow into the file. Show the person the diff.
