# Check all my Stories, however many there are

I can run `pdd test` or `pdd lint` on all my Stories at once. When they are too
many for one request, pdd sends them in parts and still gives me one result.

## Acceptance criteria

1. When my selected Stories do not fit in one upload, pdd sends them in parts that each fit. Each part has its own lint and its own source archive, and each check uses its own part's archive. I see one table, one summary line and one exit code, and stderr says how many parts there were, with the test count and size of each part.
2. A Story is never split across parts. Files that two Stories share count once in a part.
3. A Story whose files alone do not fit in one upload is refused before anything is sent. The message names the test, the size and file count it needs, and the limit. My other Stories are still sent.
4. When a lint ends before it reaches some of my tests, pdd lints those Stories again in a new part. It keeps doing this while each round gives at least one more test a verdict. A test that still has no verdict is not run, "lint did not finish". A test that has its own pass is never held back by that.
5. `pdd lint` on many Stories works the same way: one row per test, one lint state and one exit code.
6. `pdd test --read` and `pdd test --retry` of a run sent in parts read every part. A check sent again uses the archive of its own part. A run saved before parts existed reads as one part.
7. The JSON result lists the parts with their tests, source hash, file count and size. With two or more parts, the top-level source hash is null, and `pdd workflow evidence` explains that it records the result of one part only.
8. The upload limit lives in one place in pdd, with a note that names the server file it comes from. When everything fits in one part, the output is the same as before.

## Server evidence

Read from the server's main branch:

- `server/uploads.py` and `server/http_server.py`: one source upload may be at most 10 MiB and 10,000 files.
- `server/lint_driver.py`: with `complete`, the lint judges each test until a 90 s deadline (shared with the prompt lint) and lists at most 200 tests. A test it did not reach gets `not-checked`, and the lint is then not complete.

## Native cases

`test/runtime-split.test.mjs` uses the real client with `test/runtime-fake.mjs`, temporary Git and state folders, and an injected small upload limit (`uploadLimits` port). The limit is set from the real captures of the fixture Stories. No paid interpreter check or live server result is claimed.
