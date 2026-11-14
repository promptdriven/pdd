# plan

Review the map, boundaries, contracts and run order together. Each run must name
its Stories, part, slice and needs. Show which runs can start in parallel.
Put the files in the plan PR and state the open questions. Keep the small path's
PR to the map. After the PR, give `pdd product next`; normal feature runs do the
building. Do not start all runs automatically.

For a multi-part product, declare downstream work up front in `## After every tap`
in `product/plan.md`: numbered `PROMPT_PATH#OPERATION` items in execution order
(see [syntax and limits](../references/files.md#whole-product-exploration)). These
operations take empty input and share the world with the tap. Plan part-owned
app maps and referenced views for the thin journey. Surface `pdd simulate --product`
from the product checkout when the prompt drafts are ready; it reads active part
worktrees together before code generation. Keep journey run prerequisites intact:
exploring drafts does not mark a run complete or approve it.
