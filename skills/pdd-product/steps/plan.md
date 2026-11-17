# plan

Order feature runs in `product/plan.md`. Check that `## Prompts` (separate from
`## Boundaries` and `## Runs`) names how every part starts and wires its thin
`kind: native-only` boundary adapter(s) onto its checkable fake-port domain prompt(s)
(adapters depend on domain prompts, never the reverse, so Story `pdd test` never skips
with `native-only`), and that headless parts carry `0` UI screens.
Each run names its Stories, part, slice and needs; show parallel runs. Before feature
tests exist, run `pdd product status` and `pdd contracts`, and review contract examples.
Do not add placeholder tests. Put the files and open questions in the plan PR (small
maps keep only the map). After the PR, give `pdd product next`; do not auto-start runs.
