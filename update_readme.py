import re

with open('README.md', 'r', encoding='utf-8') as f:
    content = f.read()

options_old = """- `--review-only`: With `--review-loop`, run only the primary reviewer first pass. This never invokes the fixer, commits, or pushes.
- `--reviewer ROLE`: Primary reviewer role for `--review-loop` (for example, `codex`).
- `--fixer ROLE`: Fixer role for `--review-loop` (for example, `claude`). The fixer must be different from the reviewer unless `--review-only` is used.
- `--reviewers ROLES`: Legacy comma-separated review-loop role order, interpreted as `reviewer,fixer` (default: `codex,claude`)."""

options_new = """- `--review-only`: With `--review-loop`, run only the primary reviewer first pass. This never invokes the fixer, commits, or pushes.
- `--reviewer ROLE`: Primary reviewer role for `--review-loop` (for example, `codex`).
- `--fixer ROLE`: Fixer role for `--review-loop` (for example, `claude`). The fixer must be different from the reviewer unless `--review-only` is used. Acts as a fallback reviewer if the primary reviewer fails.
- `--reviewers ROLES`: Legacy comma-separated review-loop role order, interpreted as `reviewer,fixer` (default: `codex,claude`)."""

content = content.replace(options_old, options_new)

paragraph_old = """**Review-Loop Mode**: Add `--review-loop` to PR mode when you want PDD to use a primary reviewer and separate fixer on the same PR. The loop uses one isolated worktree for the PR branch, treats the reviewer as the authority, sends every valid finding to the fixer, commits and pushes successful fixes back to the PR head ref, then re-runs the same reviewer to verify the fixes and perform another full PR review. Failed pushes abort before verification, and reviewer provider failures remain not-clean."""

paragraph_new = """**Review-Loop Mode**: Add `--review-loop` to PR mode when you want PDD to use a primary reviewer and separate fixer on the same PR. The loop uses one isolated worktree for the PR branch, treats the reviewer as the authority, sends every valid finding to the fixer, commits and pushes successful fixes back to the PR head ref, then re-runs the same reviewer to verify the fixes and perform another full PR review. Failed pushes abort before verification. If the primary reviewer encounters a critical failure (e.g., auth or network error), the loop will surface diagnostic details (exit code, error class, and stderr tail) in the final report and dynamically promote the configured fixer to act as the fallback reviewer to complete the loop."""

content = content.replace(paragraph_old, paragraph_new)

with open('README.md', 'w', encoding='utf-8') as f:
    f.write(content)
