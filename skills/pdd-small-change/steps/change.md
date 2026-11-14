# change

- Complete the issue checklist in `small-change-checklist.json` (RUNBOOK §15); exclusions need issue authority.
- Edit only the approved non-PDD files (docs, guides, packages, lockfiles, config, CI, metadata or tests) — never create or edit `*.prompt.md` or `user_stories/*.md`.
- Do not edit prompt-owned files or product/app code (`src/`, `app/`, etc.) unless the person explicitly confirmed in scope; if the fix turns out to need them, stop and report back to the main chat.
- For a CI, config, package or test fix, add or update the check or test from the approved scope, never from broken output.
- Keep existing tests unless the approved plan changes them. No unrelated refactors or dependency changes.
