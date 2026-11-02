# Read test evidence for the current PR head

I can trust that test counts presented as checked evidence in a PR come from a run that pdd can see, rather than text typed by an agent.

## Acceptance criteria

1. When no current CI result or old-code proof exists, a PR does not present "Full npm test: 665/665 passed" typed in a verification note or summary as checked evidence.

## What must not change

Missing proof remains publishable with an honest not-run result. This reproducer checks the existing evidence-preparation boundary; publication refresh and output-criterion advice require separate native reproduction.
