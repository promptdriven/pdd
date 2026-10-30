# Lint source prompts before their Runtime interface exists

I can lint my plan and prose prompts before writing Runtime tests, while unfinished tests and real Runtime refusals remain visible.

## Acceptance criteria

1. An unfinished JSON test beneath test/runtime or another test or tests folder exits 2 before capture, sign-in or upload; valid Runtime tests in any folder keep ordinary discovery.
2. A proper prompt with no recognized Runtime interface is eligible source, even without a plan. A passed source lint with an empty usable prompt inventory exits 0, has no test rows and warns once for each such captured prompt that it has no Runtime interface yet.
3. Missing admission for a Runtime-bearing prompt still refuses. Recognized malformed, multiple, stale or unapproved Runtime interfaces and canonical server refusals or errors retain exit 4, including errors naming prose source.
4. Reading or retrying saved source lint preserves that capture's prose classification and warnings after files change, with no new capture, ID, POST or Check. Legacy batches or capture ports without supported classification evidence retain conservative admission.
5. Contracts, seeds and arbitrary JSON remain ordinary source. Ordinary Check, Try and selected-test lint gain no prose-source warnings from unrelated files.

## Rules to check

Only folder components test or tests add malformed or oversized JSON candidate hints; valid test discovery anywhere is unchanged. Stat an oversized candidate before any content read. Runtime block presence uses the existing preflight parser on effective captured bytes, not current disk bytes or a second parser. Absence permits only omission of a synthesized missing-admission error; explicit refused admission, refused prompt lists and global failed/refused/error results remain authoritative. Save optional prose paths only for the captured source identity; absent or unsupported metadata grants no exclusion and adds no strict gate. A successful result retains rows [], 0 AI calls and no checks sent. Warning counts follow the existing public list rule.
