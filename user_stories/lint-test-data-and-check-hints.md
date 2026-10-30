# Lint a plan beside ordinary test data and keep Check hints

I can lint a plan with ordinary test data before writing Runtime tests, and plain Check still explains an unfinished prompt.

## Acceptance criteria

1. A plan with ordinary JSON data in test/fixtures or another non-runtime test folder passes source-only lint with no test rows, no Check requests and 0 AI calls.
2. Unfinished JSON in repository-root tests or test/runtime exits 2 before capture, sign-in or upload. Oversized candidates are identified without reading their contents.
3. Program-scenario tests in any folder retain ordinary discovery and selected-test validation, including refusals for a wrong scenario version.
4. Plain Check with no tests retains the missing Runtime interface hint for a proper prompt, the other existing hints and the original five-hint limit with the remaining count.
5. Only source-only lint treats a proper prose prompt as eligible source with its own warning; it can pass with no test rows and no Check requests.
6. Reading or retrying saved source lint after files change keeps its saved classification, source identity and warnings without reading current source or posting new work.

## Rules to check

The owner prompt's candidate rule clarifies the test-folder wording in the earlier source-prompt Story: diagnostic conventions are repository-root tests recursively and repository-root test/runtime recursively. A folder named test or tests elsewhere does not itself make JSON a candidate. Existing bounded discovery of the program-scenario schema family anywhere remains unchanged; other schema families do not establish a scenario candidate. No new path restriction applies to valid test discovery. Plain Check receives the full visible hint input; only source-only lint excludes proper prompt names from that query. Classify prose from effective captured bytes, never from that hint filter or later disk contents. Canonical refusals, Runtime-bearing admission and saved-read rules retain their existing owners.
