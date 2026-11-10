# Inspect authored project files through Runtime ports

I can inspect prompts, Stories, tests, orphans and refusals through declared file and Git ports.

```pdd-boundary
prompts/cli/files.prompt.md
```

## Acceptance criteria

1. Inspecting a repository lists its prompts, Stories, orphans, refusals and warnings in path order.
2. Inspecting an unavailable repository root fails with `source-unavailable`.
3. Running `pdd files --json` inside a repository writes the JSON inventory to stdout and exits 0.
4. Running `pdd files` outside a Git repository writes a diagnostic to stderr and exits 2.
