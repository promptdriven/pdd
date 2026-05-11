import re

with open('pdd/prompts/checkup_review_loop_python.prompt', 'r', encoding='utf-8') as f:
    content = f.read()

content = content.replace(
    "3. Dataclasses (all dataclasses must be importable from this module): `ReviewLoopContext`, `ReviewLoopConfig`, `ReviewLoopState`, `ReviewFinding`, `ReviewResult`, `FixResult`.",
    "3. Dataclasses (all dataclasses must be importable from this module): `ReviewLoopContext`, `ReviewLoopConfig` (must include `reviewer_fallback: bool` defaulting to `True`), `ReviewLoopState`, `ReviewFinding`, `ReviewResult`, `FixResult`."
)

findings_model_header = "% Findings model\n13. Normalize reviewer output into"
findings_model_new = "% Findings model\n12o. `ReviewResult` and `ReviewLoopState` must capture and track `status_reason`, `exit_code`, `stderr_tail`, and `error_class`. Capture the last 20 lines of `stderr`, the exit code, and the error classification (e.g., auth, network, timeout, crash) from the reviewer subprocess, and populate them into `ReviewResult`.\n13. Normalize reviewer output into"
content = content.replace(findings_model_header, findings_model_new)

final_report_header = "% Final report\n26. Begin the report with `## Step 7/8: Review Loop Final Report`. Required keys, in order:"
final_report_new = "% Final report\n25a. Bubble up failure diagnostics (`status_reason`, `exit_code`, `error_class`, and `stderr_tail`) into the final report comment (in the per-reviewer status table or a dedicated diagnostics section) when a critical failure occurs, making them actionable for users and the retry orchestrator.\n26. Begin the report with `## Step 7/8: Review Loop Final Report`. Required keys, in order:"
content = content.replace(final_report_header, final_report_new)

loop_semantics_header = "% Loop semantics\n16. The primary reviewer runs first in `mode=\"review\"`."
loop_semantics_new = "% Loop semantics\n15b. Implement promote-on-failure: If the primary reviewer ends in a `HARD_NOT_CLEAN` state (like `failed`, `degraded`, or `missing`) and `config.reviewer_fallback` is enabled, dynamically run the same review pass using the configured secondary reviewer (the fixer). If the secondary reviewer succeeds, the loop can complete successfully, noting in the report that the primary was unavailable.\n16. The primary reviewer runs first in `mode=\"review\"`."
content = content.replace(loop_semantics_header, loop_semantics_new)

with open('pdd/prompts/checkup_review_loop_python.prompt', 'w', encoding='utf-8') as f:
    f.write(content)
