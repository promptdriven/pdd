## Summary

This PR addresses the issue where the review loop final report shows 'codex=failed' without actionable diagnostics and fails to fallback to a secondary reviewer. It surfaces failure details (exit code, error class, stderr tail) into `ReviewLoopState` and the final report. It also introduces a promote-on-failure mechanism where the secondary reviewer acts as a fallback if the primary reviewer fails with a hard error.

Closes #922

## Changes Made

### Prompts Modified
- `pdd/prompts/checkup_review_loop_python.prompt` - Added fallback support and captured failure diagnostics.
- `pdd/prompts/agentic_checkup_python.prompt` - Updated function signature to accept fallback parameters.

### Documentation Updated
- `README.md` - Added documentation for the new fallback behavior and `--no-reviewer-fallback` option.

## Review Checklist

- [ ] Prompt syntax is valid
- [ ] PDD conventions followed
- [ ] Documentation is up to date

## Next Steps After Merge

1. Regenerate code from modified prompts in dependency order:
   ```bash
   ./sync_order.sh
   ```
   Or manually:
   ```
   pdd sync checkup_review_loop
pdd sync agentic_checkup
pdd sync checkup
   ```
2. Run tests to verify functionality
3. Deploy if applicable

---
*Created by pdd change workflow*