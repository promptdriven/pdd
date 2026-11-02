# See exactly what one area Try sends

I can open a Try of one area of a large repository, and see beforehand exactly which files it sends, without the tests of the other Stories.

## Acceptance criteria

1. A Try with an app map sends the app map, its stylesheets, the prompts its screens and handlers name with their declared dependencies, and the one seed Story with its test. It sends no test of another Story, also when all tests together are over the upload limit.
2. `pdd test --files STORY --app-map MAP` lists exactly the files and byte sizes that `pdd simulate STORY --app-map MAP` sends, offline and without sign-in. A test path given as STORY works the same way. A Story with two test files is refused as in 3, and both files are listed to choose from.
3. `pdd test --files --app-map MAP` with no Story, or with several Stories, is refused with exit 2. The message says that a Try starts from one Story, tells me to name the Story that seeds the Try, and lists the Stories to choose from. It lists no files and reports no size. A bad map is reported before the Story choice, as by `pdd simulate`.
4. When a file that the map declares is missing, the Try and the listing are refused before sign-in or upload, and the message names the map and the missing path.
5. `pdd test --files` without `--app-map` still lists a check of the selected Stories. When that upload is over the limit, pdd says so and names the largest files with their sizes.

## Rules to check

A Try never sends a file because it is in the repository. It sends a file only because the map, the seed test or a declared dependency names it. A listing never shows an upload that no command sends. A missing declared file is never left out silently.

Runtime check: NOT REPLAYED. Upload capture reads Git, the file system and tar output, which have no executable Runtime port in the owning prompts. `test/try-sends-its-map-closure.test.mjs` records the cases as ordinary Node tests; it is not an interpreter scenario or an approval.
