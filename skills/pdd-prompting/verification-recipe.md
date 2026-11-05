# Verification recipe: <affected behavior>

Replace the placeholders with commands and expected observations that another agent can use from a fresh checkout. Keep this recipe and its required entry points and controlled fixtures in project source. The approved Story is the authority for expected behavior.

- Story and scope: <Story path and behavior covered>
- Public boundary: <user action, CLI, public API, protocol or artifact consumer>
- Prerequisites and dependencies: <versions, local services, access; identify simulated dependencies and their limits>
- Preparation and isolation: <install/build commands, isolated data and resource locations>
- Start and readiness: <commands and observable readiness; say why not applicable if none>
- Action: <actual action and controlled input>
- Expected results: <visible output, status and meaningful side effects from the Story>
- Evidence: <commands and observed results, candidate revision, issue, UTC time, verifier/session, evidence type and limitations; retain outside the checkout>
- Cleanup: <commands to remove only isolated resources; preserve evidence>

For a bug, use the same expectation on old and corrected code and record the old assertion failure and corrected result. A setup error or crash is not proof of the claimed semantic defect. If a dependency or action is unavailable, record the unproved scope and reason; do not call it a pass. Keep native behavior, integration and prompt-interpreter results distinct, and use the existing replay and checker verdicts.
