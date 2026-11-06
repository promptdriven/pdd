# Verification recipe: <affected behavior>

Replace the placeholders with commands and expected observations that another agent can use from a fresh checkout. Keep this recipe and its required entry points and controlled fixtures in project source. The approved Story is the authority for expected behavior.

- Story and scope: <Story path and behavior covered>
- Public boundary: <user action, CLI, public API, protocol or artifact consumer>
- Prerequisites and dependencies: <versions, local services, access; identify simulated dependencies and their limits>
- Preparation and isolation: <install/build commands, isolated data and resource locations>
- Start and readiness: <commands and observable readiness; say why not applicable if none>
- Source/artifact association: <actual entry point and loaded source modules or built artifact, revision and local changes affecting it, dependency lock and helpers; reuse existing identities and say when a stage or artifact is not applicable>
- Stage results: <source/context; composition/dependencies; build or compile; test collection; readiness; intended boundary; criterion checks; each result or reason it did not run>
- Required case inventory: <all existing required Story criteria and case/test IDs; mark passed, failed, blocked before target, skipped or unexecuted, and name the target reached>
- Action and expected results: <actual user action and the Story's visible results and meaningful side effects>
- Evidence and failures: <commands, observed results, original failure, candidate revision, issue, UTC time, verifier/session, evidence type and limitations; retain outside the checkout>
- Cleanup: <commands and actual result for removing only isolated resources; preserve evidence and report cleanup failures separately>

For a bug, use the same expectation on old and corrected code and record the old assertion failure and corrected result. A setup error or crash before the target is not proof of the claimed semantic defect or a mutation kill. If a dependency or action is unavailable, record the unproved scope and reason; do not call it a pass. Keep native behavior, integration and prompt-interpreter results distinct, and use the existing replay and checker verdicts.
