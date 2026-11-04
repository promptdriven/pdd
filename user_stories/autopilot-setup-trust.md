# See trusted people during setup

As a repository maintainer, I can see who is trusted during setup, so that I can add anyone else.

## Acceptance criteria

1. Setup shows owner Ada and write collaborators Bo and Cy.
2. An empty additional names answer adds nobody.
3. Setup warns when the trusted list may be incomplete and continues.
4. Setup warns and continues when GitHub provides neither owner nor writers.
5. If GitHub does not answer within a short time, setup warns that the trusted list may be incomplete and continues, keeping confirmed people trusted without trusting unconfirmed people.

## Rules to check

- Native test: stall each GitHub process in turn; setup must proceed within a short bound and terminate the stalled child. A confirmed owner remains trusted if the collaborators lookup stalls. The runtime fixture supplies incomplete data and cannot simulate elapsed time or child termination.

- A failed file write reports a clear error, exits nonzero and leaves `pdd.json` unchanged. Native test: inject a failed write and inspect the original file.
- Setting a mode starts no run or interpreter. Native test: spy on workflow and interpreter dispatch.
