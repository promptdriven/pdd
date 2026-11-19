---
name: pdd-product
description: Use when a person asks to plan a multi-part product roadmap with shared contracts and staged feature runs across independent parts.
metadata:
  pdd-skills: 0.1.38
---

# PDD product

Start with the person's product request. Find or make its product issue, for example
`gh issue create --title "Product: coffee pickup" --body "<the request>"`, then run
`pdd workflow run product ISSUE`. This workflow makes and tracks the plan.
Normal feature runs build the parts.

1. map: steps/understand.md, steps/map.md → gate: approve
2. plan: steps/parts.md, steps/contracts.md, steps/plan.md → gate: pr

## Rules

- Read pdd-prompting before writing Stories or contracts (`1` Story per cohesive standalone user loop). Keep one coupled slice in 1 session (0 authoring subagents) and check `pdd files` + `pdd lint --local`; across independent decoupled modules, lock shared contracts first and parallelize independent workers.
- The person approves the map, then reviews the plan PR. Never decide their open questions or approve for them. Never merge.
- Size the plan by architecture boundaries rather than fixed Story counts: for a single cohesive part, keep `product/map.md` only and run one feature run; for multiple decoupled parts, define parts, shared contracts and planned runs; for broad cross-part rollouts, also define vertical slices where slice 1 is one thin end-to-end journey through the parts. The person can change the path.
- Keep the plan in repo files. Use [the file formats](references/files.md). A product piece is a part; an area is a workflow phase.
- Keep each planned run scoped to one cohesive part or contract boundary; warn without refusing when a planned run mixes unrelated parts.
- Parts share contracts, not code. Feature tests use the other parts as fakes from those contracts. Contract changes go through a plan PR.
- Parallel runs are optional. After the plan PR, show `pdd product next` and let the person start runs in parallel or in order.
- In a run, use `pdd workflow done STEP --summary "one line"` and `pdd workflow ask "question"`. Write notes in the run folder. Keep receipts and logs outside the repo.
