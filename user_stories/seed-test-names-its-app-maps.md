# Keep one test as my Story's test and my Try's seed

I can name, in my Story's test, the app map that a Try starts with. Then lint and the check of my Story send that map and its prompts, so the test can bind what the map's taps call, and my Story stays green.

## Acceptance criteria

1. When my test lists an app map in `app_maps`, `pdd test --files STORY` lists that map, its stylesheets and the prompts that its screens and handlers name, with their declared dependencies, next to my Story's own files. No `--app-map` option is needed.
2. A check (`pdd test STORY`) and a lint (`pdd test --lint STORY`) of that test send the same files: the declared map and its closure are in every upload. Local preflight does not refuse the test for its `app_maps` key.
3. When a map that my test lists is missing, the listing, the lint and the check are refused before sign-in or upload, and the message names my test and the missing path.
4. `pdd test --lint STORY --app-map MAP`, and `pdd test STORY --app-map MAP`, are refused with exit 2. The message says that `--app-map` works only with `pdd simulate` and `pdd test --files`, and that a test names the maps it seeds in `app_maps`. Nothing is sent.
5. A test without `app_maps` sends the same files as before.
6. `pdd simulate STORY` with no `--app-map` starts the Try with the one map that the test lists in `app_maps`. A `--app-map` that the test does not list, or several listed maps and no `--app-map`, is refused with exit 2 that names the listed maps, and nothing is sent.

## Rules to check

A test declares the maps it seeds; pdd never guesses them from the repository. Lint, the check and the Try then send and judge the same operations. A missing declared file is never left out silently.

Runtime check: NOT REPLAYED. Upload capture reads Git, the file system and tar output, which have no executable Runtime port in the owning prompts. `test/seed-test-names-its-app-maps.test.mjs` records the cases as ordinary Node tests; it is not an interpreter scenario or an approval. The interpreter side (accepting the bindings) is a separate prompt-runtime change.
