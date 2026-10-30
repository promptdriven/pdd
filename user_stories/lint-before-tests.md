# Lint a product plan before tests exist

I can lint the source I have while I plan a product, before I write feature tests.

## Acceptance criteria

1. With a Git-visible coffee product map, plan, shared contracts and seed, but no prompts or Story tests, `pdd check --lint` sends the existing source for complete lint and a confirmed pass exits 0 with "No tests yet", "0 AI calls" and "No checks were sent".
2. With prompts or part seeds and no Story tests, unqualified remote lint includes that source and its required dependencies, while unrelated repository files stay out.
3. A source-only lint refusal or error remains a refusal with exit 4 and its diagnostics; pending or unknown lint remains exit 3. JSON has no Story rows and never turns an empty list into a pass.
4. Reading a pending source-only lint reads the same saved result, reports its real outcome and never starts a check or Try.
5. Unsafe, missing, oversized or repeatedly changing required source is refused by the ordinary capture rules before upload, and invalid Runtime limits are refused before sign-in.
6. An empty repository or an explicit unknown Story still exits 2; ordinary Check, Try and local drawing lint retain their selection and behavior.

## Rules to check

Only unqualified remote lint with zero discovered program-scenario tests can
select source without tests. Use existing Git-visible plan/map, contracts,
prompts and part seeds; never manufacture a Story or scenario. Includes,
dependencies, references and capture safety apply normally. A pass requires
confirmed successful source lint; refusals, errors and uncertainty cannot be
hidden by zero Story rows. Saved reads never grant permission to dispatch work.
