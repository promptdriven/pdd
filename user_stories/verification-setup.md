# Verify a repository's real behavior

I can give PDD an existing repository and have an independent verifier repeat the approved behavior from a fresh checkout, even when the repository has no verification recipe yet.

## Acceptance criteria

1. PDD examines the repository's documentation, manifests, CI and tests to find its product boundary and any usable setup before choosing or creating a recipe.
2. When setup is missing, PDD keeps the smallest repeatable setup and controlled data needed for the affected behavior in the repository and runs it. The recipe covers preparation, readiness, the action, observable results and side effects, and cleanup.
3. The verifier follows the approved Story at the real public boundary and keeps its results and evidence separate from prompt-interpreter results. A simulated dependency does not establish a real integration pass.
4. A fresh verifier can repeat the recipe in an isolated fresh checkout without private conversation context. Cleanup leaves retained evidence available outside the checkout.
5. An unavailable dependency, failed setup or unexecuted action is reported with its scope and reason; it is not reported as a behavior pass. A new product remains in prompt space until code is authorized.
6. For a bug, the same intended expectation exposes the claimed old behavior and passes on corrected code; an old-code crash or setup failure is not a semantic failure.

## Rules to check

Expected behavior comes from the approved Story. A setup success alone, a simulated integration, an unrelated screenshot or exit status alone must not be reported as proof of the affected behavior. Preserve existing independent checker verdicts and replay evidence rather than creating another approval authority.
