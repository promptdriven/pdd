# See trusted people during setup

As a repository maintainer, I can see who is trusted during setup, so that I can add anyone else.

## Acceptance criteria

1. Setup shows owner Ada and write collaborators Bo and Cy.
2. An empty additional names answer adds nobody.
3. Setup warns when the trusted list may be incomplete and continues.
4. Setup warns and continues when GitHub provides neither owner nor writers.

## Rules to check

- A failed file write reports a clear error, exits nonzero and leaves `pdd.json` unchanged. Native test: inject a failed write and inspect the original file.
- Setting a mode starts no run or interpreter. Native test: spy on workflow and interpreter dispatch.
