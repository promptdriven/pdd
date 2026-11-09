# Read late evidence in long step summaries

As a PR reviewer, I want to read important outcomes, limitations and public references from long step summaries, so that a body-size cut does not hide evidence I need.

## Acceptance criteria

1. When a long summary ends with `Limitation: upstream failure remains DEFERRED; https://github.com/example/upstream/issues/476` after ordinary notes, the reviewer can read that limitation and public reference on GitHub even when the summary must be shortened.
2. When several summaries must be shortened, the complete cleaned summaries are readable through confirmed links on the PR in their original step and line order; each shortened summary says how much cleaned text was omitted.
3. The whole PR body stays within 60,000 Unicode code points; cuts do not split a Unicode code point or a URL, and an omission is never silent.
4. A new PR shows recovery as pending until its full recovery copy is confirmed; failure retains that PR without creating a duplicate. If recovery publication fails or its result is uncertain, the PR does not claim full recovery; an uncertain write is checked before any retry, and an update keeps the last confirmed recovery links until the new copy is confirmed.
5. Every recovery comment, including its index, stays within 60,000 Unicode code points; if an indivisible URL or the ordered index cannot fit, publication fails before comment writes and the previous PR body remains.
6. Recovery links identify only matching comments on the same PR from the publishing actor; unrelated or ambiguous comments do not establish recovery.
7. Summary text remains plain text and retains the existing cleaning, private-link and local-path restrictions; a local run-folder pointer alone does not give a GitHub reviewer access to omitted evidence.

## Rules to check

The body budget is 60,000 Unicode code points including all wrappers and notices. Forbidden results include making the late limitation and reference in criterion 1 unavailable on GitHub, exposing a private link, splitting a URL or Unicode code point, or claiming recovery before all linked text is confirmed. A comment or index over 60,000 code points and splitting an indivisible URL are forbidden; preflight failure leaves the previous body intact.

## What must not change

The existing top evidence, verification material, summary sanitation, inert rendering, ownership marker and PR update protections remain in force.
