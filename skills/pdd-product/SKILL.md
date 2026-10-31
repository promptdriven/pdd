---
name: pdd-product
description: Use when a person wants to build a whole product from one sentence and needs a story map, parts, shared contracts and a plan of feature runs.
metadata:
  pdd-skills: 0.1.12
---

# PDD product

Start with the person's sentence. Find or make its product issue, for example
`gh issue create --title "Product: coffee pickup" --body "<the sentence>"`, then run
`pdd workflow run product ISSUE`. This workflow makes and tracks the plan.
Normal feature runs build the parts.

1. map: understand, map → gate: approve
2. plan: parts, contracts, plan → gate: pr

## Rules

- Read pdd-prompting before writing Stories or contracts. The main chat coordinates. Run each step in a fresh subagent with its step file and paths.
- The person approves the map, then reviews the plan PR. Never decide their open questions or approve for them. Never merge.
- Count CORE Stories and parts in the map. Recommend small for about 10 Stories and 1 part, medium for 10–50 Stories and 2–5 parts, large for more than 50 Stories or more than 5 parts. The person can change the path.
- Small: keep `product/map.md` only and run one feature run. Medium: make parts, contracts and planned runs. Large: also make slices; slice 1 is one thin journey through all parts.
- Keep the plan in repo files. Use [the file formats](references/files.md). A product piece is a part; an area is a workflow phase.
- Aim for at most about 12 Stories or 5 new prompts per planned run. Warn for larger runs; do not refuse them.
- Planning checks contracts locally with `pdd contracts --check`, with no PDD interpreter lint, test or simulation. Each part's first interpreter lint/test waits for its prompt, Stories and tests in its feature run.
- Parts share contracts, not code. Feature tests use the other parts as fakes from those contracts. Contract changes go through a plan PR.
- Parallel runs are optional. After the plan PR, show `pdd product next` and let the person start runs in parallel or in order.
- In a run, use `pdd workflow done STEP --summary "one line"` and `pdd workflow ask "question"`. Write notes in the run folder. Keep receipts and logs outside the repo.
