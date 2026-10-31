# Reuse unchanged Story checks

I can check my changed work quickly and return to failures without paying for unchanged passing Stories.

## Acceptance criteria

1. I can repeat `pdd test` without changing my files and see unchanged Stories with their previous pass time, zero current AI calls and the number of skipped Stories.
2. Changing a reached prompt, shared dependency, starting data, test or Story reruns exactly the affected Stories in my selected scope; unrelated Stories stay skipped.
3. A Story is reused only after all its test files passed; failed, refused, not-run, unknown or interrupted attempts cannot reuse an older pass.
4. `pdd test --lf` runs the latest failed Stories in my selected scope; no failures in that scope uses the normal selected Stories and unchanged passes may be skipped.
5. `pdd test --cache-clear` clears the whole local cache and sends my selected Stories again; it takes precedence over `--lf`, prints one stderr notice with the selected Story count, and the interpreter may return a saved answer for the same key.
6. A damaged or unsafe cache runs my selected Stories with one warning, leaves outside files untouched and never treats damaged data as a pass.
7. The local `.pdd/cache/test/` folder is Git-ignored in my repository, including a linked worktree.
8. I can select tests by Story, test file, Story file or directory relative to my current folder; ordinary test and its accepted former name use the same cache.

## Rules to check

Reuse is local prior evidence. A changed or incomplete Story must never look freshly checked or cost zero calls merely because an older version passed. A cache failure must never block the check or touch an outside path. A clear request keeps normal selection and takes precedence over last-failed filtering.

Confirmed completed saved reads update the cache; running results never count as passes. The cache uses `stories.json` and reads validated `lastfailed.json` for `--lf`. Missing last-failed metadata after a cache exists, damage or inconsistency runs selected work fresh with one warning and heals after completion. Deleted Stories are pruned; existing failures outside my selection remain recorded.

A Git-tracked cache or one copied without this machine's external state must run checks, including when those checks fail. My last failure remains in `--lf` after sign-in failure, interruption, timeout or any other attempt without a verdict, until a confirmed pass. A change to pdd version, local engine, interpreter origin, call budget, reached call target or exact authored bytes prevents reuse. Server engine/model updates require `pdd test --cache-clear` because zero-call reuse cannot discover them; the interpreter may still return a saved answer for the same key. A saved pass retains its observed server engine identity.

A damaged regular cache heals after the completed check, warns once and names `pdd test --cache-clear`. A dead-owner lock recovers with one warning, also during clear, while live owners stay protected. Symlinked ancestors of my external state folder work; a final state-folder symlink is refused.

Runtime check: NOT RUN; this Story's orchestration, Git, clock and filesystem effects are native-only. The supplied JSON cases are replayed by `node --test test/test-cache.test.mjs` against a fake interpreter; no model or live service is used.
