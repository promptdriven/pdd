# Bundled guidance loading

Own `src/guidance.mjs`; export `loadGuidance({packageRoot,cwd})` returning full instruction text. This is only the old runner's stage context, not a new validator/installer. When the new runner lands, nothing uses loadGuidance: delete this module and prompt then. `pdd session` does not use it: the short [session intro](session-intro.prompt.md) replaces pasted guidance. Read the complete canonical docs/prompting-guide.md FIRST, then skills/pdd/SKILL.md and all regular Markdown files recursively under skills/pdd/references. Include absolute package root/current cwd and require the agent to summarize the relevant guide method before ANY Story drafting; a link is not loaded context. Preserve the full original file text, never truncate/copy the guide to another file. Read the complete bundle before successful output. Missing required files/read failure is an error; do not follow symlinked directories/files. Explicit workflow.run/resume uses the separate local runner; its current-stage instructions own progression and PR effects. Do not contradict that authority. Existing project instructions remain native-owned through cwd, not copied into the package.

## Dependencies

Read the full [Prompting guide](../../docs/prompting-guide.md) before Stories. Follow [alpha boundary](public-boundary.prompt.md).

## Installed command identity in native shells

Normal native tool login shells can override inherited PATH and resolve a different `pdd` installation. In every loadGuidance result, include the actual current process.execPath and absolute packageRoot/bin/pdd.mjs entry as a literal argv pair and safely shell-quoted command prefix. Instruct the agent to use that exact absolute invocation for PDD discovery/actions instead of bare pdd, even if command -v pdd returns another installation. Preserve inherited native environment/settings; no PATH/global profile edits, wrappers, config/auth copying, or extra launcher layer. This prefix identifies this installed package and does not authorize effects by itself. Full original canonical guide/skill loading and guide-before-Story rule remain unchanged.
