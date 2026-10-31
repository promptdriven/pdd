# Reuse unchanged Story checks

I can check my changed work quickly and return to failures without paying for unchanged passing Stories.

## Acceptance criteria

1. I can repeat `pdd test` without changing my files and see unchanged Stories with their previous pass time, zero current AI calls and the number of skipped Stories.
2. Changing a reached prompt, shared dependency, starting data, test or Story reruns exactly the affected Stories in my selected scope; unrelated Stories stay skipped.
3. A Story is reused only after all its test files passed; failed, refused, not-run, unknown or interrupted attempts cannot reuse an older pass.
4. `pdd test --lf` runs the latest failed Stories in my selected scope; no history runs the selected Stories and known history with no failures runs none.
5. `pdd test --cache-clear` clears the whole cache and runs all Stories, even when a path or `--lf` is also supplied.
6. A damaged or unsafe cache runs my selected Stories with one warning, leaves outside files untouched and never treats damaged data as a pass.
7. The local `.pdd/test-cache/` folder is Git-ignored in my repository, including a linked worktree.
8. I can select tests by Story, test file, Story file or directory relative to my current folder; ordinary test and its accepted former name use the same cache.

## Rules to check

Reuse is local prior evidence. A changed or incomplete Story must never look freshly checked or cost zero calls merely because an older version passed. A cache failure must never block the check or touch an outside path. A clear request takes precedence over selection and last-failed filtering.

Runtime check: NOT RUN; this Story's orchestration, Git, clock and filesystem effects are native-only. The supplied JSON cases are replayed by `node --test test/test-cache.test.mjs` against a fake interpreter; no model or live service is used.
