# plan

Review the map, boundaries, contracts and run order together. Each run must name
its Stories, part, slice and needs. Show which runs can start in parallel.
Run `pdd contracts --check` for the local contract result; do not call server
lint/check or Try while planning. The first server lint/check belongs to each
part's feature run once its prompt, Stories and tests exist.
Put the files in the plan PR and state the open questions. Keep the small path's
PR to the map. After the PR, give `pdd product next`; normal feature runs do the
building. Do not start all runs automatically.
