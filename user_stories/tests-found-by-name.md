# Find each Story's test by its name and folder

I can keep the test of a Story in a `tests` folder under the Story's name, at any size, and pdd finds it, checks the whole file and tells me about every Story and test file that it cannot use.

## Acceptance criteria

1. The test of Story `user_stories/S.md` (also in a subfolder of `user_stories`) is `S.json` in a folder named `test` or `tests`, at any depth: `tests/S.json`, `tests/runtime/S.json` and `runtime/tests/S.json` all count. A second test for another starting world is named `S.<world>.json`, for example `tests/S.empty-shop.json`. pdd finds tests by their names and folders and does not open other JSON files to find tests.
2. A 2,408,687-byte test `runtime/tests/m1-big.json` whose `schema_version` comes after the first 64 KiB is found, `pdd test m1-big` selects it, and pdd reads and checks the whole file.
3. A Story with no test prints one line with the exact expected path, for example `Warning: user_stories/phone/p17.md has no test: expected tests/p17.json (or p17.json in any test or tests folder).`
4. `pdd test p17` for that Story stops with exit 2 and the same sentence, not "Unknown story".
5. JSON files in `test` or `tests` folders whose names match no Story print one line, for example `Warning: tests/notes.json matches no Story (user_stories/**/notes.md).`, or `Warning: 2 JSON files in test folders match no Story (…). pdd test --files lists them.` for more than one; `pdd test --files` and `--json` list each file.
6. Two files with the same name for one Story, for example `test/runtime/p17.json` and `tests/p17.json`, are an error that names both files, and pdd checks neither of them, also with `pdd test --lint`. A file name that fits two Stories, such as `tests/a.b.json` with Stories `a` and `a.b`, is an error that names both Stories.
7. A selected test that is not valid JSON, cannot be read or is over the upload limit is refused with its file name, and the other Stories still run. A test whose `story_path` names another Story is refused with the test, its Story and the other Story.
8. `pdd test nope` stops with exit 2 and lists every Story with its test file, or with "no test" and the expected path.
9. One test file has no size limit. The only size limit is the upload limit of 10 MB and 10,000 files; over it, pdd names the largest files with their sizes and the limit.
10. When the interpreter says that it can lint named tests, the lint request names the selected tests, so the interpreter lints exactly those files.

## Rules to check

A test is a fact that the author declares by the file's name and folder, never a guess from the file's content. pdd never skips a file without a line that names it. Discovery reads Story files, never JSON files; it reads a JSON file only after the rule matched it to a Story.

## Native verification boundary

Discovery reads the person's files and Git; the lint request goes to the interpreter. These are native effects. Node tests check them with real temporary Git repositories and a fake interpreter. The same discovery ran offline on clones of pdd, snake and agent-link (see the PR).
