# plan

Review the map, boundaries, contracts and run order together. Each run must name
its Stories, part, slice and needs. Show which runs can start in parallel.
Before feature tests exist, run `pdd product status` for structural problems (it
may read GitHub), and `pdd contracts` for an inventory, not schema validation.
Manually review contracts with normal, refusal and empty-world examples and
domain boundaries. Hosted `pdd lint` needs Story tests; `pdd lint --local` is
partial and does not validate shared schemas. Do not add placeholder tests.
Once feature tests exist, `pdd test` includes lint.
Put the files in the plan PR and state the open questions. Keep the small path's
PR to the map. After the PR, give `pdd product next`; normal feature runs do the
building. Do not start all runs automatically.
