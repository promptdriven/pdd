# Recognize unfinished tests and read source lint safely

I can distinguish source lint from an unfinished test, read its saved result safely, and see every warning.

## Acceptance criteria

1. With a plan and an unfinished test candidate or misnamed prompt, remote lint exits 2 with ordinary selection help before capture, sign-in or upload; valid selected tests keep their ordinary path.
2. With no candidates, contracts, seeds and unrelated JSON do not block legitimate source lint, while an empty or unrelated-only repository and an explicit unknown Story still exit 2.
3. Retrying source-only lint reads its saved result, says there is nothing to retry as information, reports the real state and exit, and sends no work or duplicate result.
4. Broken unreferenced contracts and seed worlds stay warnings. Success shows every warning, including a Story with no test, and ends with "Source lint passed with N warnings" when warnings exist, plus "No tests yet", "0 AI calls" and "No checks were sent".
5. Help explains source lint before tests exist; ordinary Check, Try, selected-test retry and local drawing lint retain their behavior.

## Rules to check

Fallback requires zero discovered tests and zero candidate hints. Oversized JSON beneath a test or tests folder component is a candidate without being read; do not broaden discovery to arbitrary JSON. A proper prompt without a recognized Runtime interface is ordinary source with its own warning, not an unfinished test candidate. Its missing inventory row alone cannot refuse source lint; actual Runtime blocks and canonical server errors/refusals retain admission rules. Saved source classification and warnings survive disk changes; absent legacy classification remains conservative. Source-only retry cannot capture, allocate an ID, POST or dispatch a Check, regardless of cached or refreshed outcome. N counts public warnings entries plus problems entries with severity warning, after existing owner deduplication, each once; informational retry advice is excluded. Errors, refusals, uncertainty and access failures keep their nonzero exits with empty rows.
