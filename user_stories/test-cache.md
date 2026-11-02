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
8. I can select tests by Story, test file, Story file or directory relative to my current folder; the canonical `pdd test` command uses this cache.
9. I reuse passes only when their interpreter identity is known and they are at most seven days old; an older pass runs again. A build or model change found during my run also runs the selected Stories it initially skipped.
10. A Story using the real clock or an AI-played fake runs every time and says why. Fully deterministic supplied replies and a fixed clock can still reuse a complete pass.
11. When `CI` is unset or is the empty string, `0` or `false`, unchanged passes may be reused; every other value runs every selected Story. A saved pass at most seven days old still counts for prompt approval.

## Rules to check

Reuse is local prior evidence. A changed or incomplete Story must never look freshly checked or cost zero calls merely because an older version passed. A cache failure must never block the check or touch an outside path. A clear request keeps normal selection and takes precedence over last-failed filtering.

Confirmed completed saved reads update the cache with the original sample time; reading an old answer later never makes it fresh. Running results never count as passes. Uncertain resource kinds, unknown actions, prompt-played store bindings and unavailable sources run and explain why. Only selected tests’ reached declarations matter; a plain dependency need not declare an interface. Only one clean record with the same known build and model can permit reuse. A run saves its in-progress mark before sending checks. Another run's mark, even after a crash, prevents reuse. A short run inside a longer run sends checks; a run after a crash also sends checks. A failed sign-in removes its own mark and leaves doubt. A saved read saves its own mark before it can continue held checks or resend restarted checks; its finish leaves doubt. Clearing the cache keeps every in-progress mark. Finished runs remove their own marks, and one later clean run restores reuse. Overlap, reads (even when they resend), old or unknown writers, partial or mixed observations, and multiple stored values leave doubt and run until a clean normal run restores evidence. After a timeout or interrupt, affected skips become not sent with a reason; the original running-job recovery command remains visible. The cache uses `stories.json` and reads validated `lastfailed.json` for `--lf`. Missing last-failed metadata after a cache exists, damage or inconsistency runs selected work fresh with one warning and heals after completion. Deleted Stories are pruned; existing failures outside my selection remain recorded.

A Git-tracked cache or one copied without this machine's external state must run checks, including when those checks fail. My last failure remains in `--lf` after sign-in failure, interruption, timeout or any other attempt without a verdict, until a confirmed pass. A change to pdd version, interpreter origin, call budget, reached call target or exact authored bytes prevents reuse. A saved pass retains the interpreter build and requested model from its answers. Missing or conflicting identity never authorizes reuse. When another answer in my run reveals a changed build or model, Stories skipped in that run also run, with a reason. An all-skipped run cannot discover server changes without calls.

A damaged regular cache heals after the completed check, warns once and names `pdd test --cache-clear`. A dead-owner lock recovers with one warning, also during clear, while live owners stay protected. Symlinked ancestors of my external state folder work; a final state-folder symlink is refused.

Prompt tests: NOT RUN; this Story's orchestration, Git, clock and filesystem effects are native-only. The supplied JSON cases are replayed by `node --test test/test-cache.test.mjs test/test-cache-v3.test.mjs test/test-cache-fixes.test.mjs test/test-cache-round2.test.mjs test/test-cache-round3.test.mjs` against a fake interpreter; no model or live service is used.
