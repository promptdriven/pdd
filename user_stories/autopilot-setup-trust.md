# See trusted people during setup

As a repository maintainer, I can see who is trusted during setup, so that I can add anyone else.

## Acceptance criteria

1. Setup shows owner Ada and write collaborators Bo and Cy.
2. An empty additional names answer adds nobody.
3. Setup warns when the trusted list may be incomplete and continues.
4. Setup warns and continues when GitHub provides neither owner nor writers.
5. If GitHub does not answer within a short time, setup warns that the trusted list may be incomplete and continues, keeping confirmed people trusted without trusting unconfirmed people.

## Rules to check

- Native test: stall each GitHub lookup in turn; its budget is 5 seconds, followed by a bounded termination grace for only its owned child processes. Setup continues and terminates the stalled owned children. A confirmed owner or writers remain trusted if another lookup stalls; unknown people never become trusted. The budget is internal, with no public setting. The runtime fixture supplies incomplete data and cannot simulate elapsed time or child termination.

- A failed file write reports a clear error, exits nonzero and leaves `pdd.json` unchanged. Native test: inject a failed write and inspect the original file.
- Setting a mode starts no run or interpreter. Native test: spy on workflow and interpreter dispatch.
