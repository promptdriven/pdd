# Read my saved lint result

I can read my saved lint result and tell that it passed without sending the lint again or starting a Story check.

## Acceptance criteria

1. After `pdd lint place-order --timeout 1` returns a pending batch, reading that batch with `pdd test --read BATCH` after its one selected test passes lint prints "Lint: 1 of 1 tests pass. 0 AI calls. No checks were sent." and exits 0; with `--json`, the summary is the same and the row state is `passed`.
2. Reading the same standalone lint batch after the original lint already passed gives the same passing summary, exit 0 and `passed` JSON row.
3. Reading a standalone lint batch that finished refused shows its refusals and exits 4; its JSON row state is `refused`.
4. These standalone lint reads send no new lint or Story check and do not advise starting a fresh check. Reading a normal Story check held for lint still continues that original check with its saved selection and ceiling of 6 calls, without repeating lint.

## Rules to check

A confirmed passing standalone lint must not become `not_run`, exit 5 or a `lint-finished` reason just because no Story check was requested. Both pending-first and already-passed histories retain the lint summary in text and JSON. A refusal must not become a pass. Standalone lint reads must not send a fresh lint or a paid Story check.

The existing [saved Check intent policy](../prompts/cli/runtime-client.prompt.md#continue-the-original-saved-check) still decides ambiguous or legacy intent; this Story changes no such classification or normal Check continuation rule. A passing lint alone does not authorize a Story check. The broader preservation cases remain in [Continue my check after slow lint](runtime-lint-continuation.md).

## Cases and Runtime boundary

[Native draft cases](../test/runtime/read-saved-lint-cases.json) record the requirement-derived expected results for this issue and its refusal/normal-Check controls. They are not executable Runtime scenarios or a claim of native replay coverage.

Runtime check: BLOCKED (#2548). The owner, [Runtime client](../prompts/cli/runtime-client.prompt.md), has no Runtime interface for its real public boundary. Git discovery/source capture, archive/hash, private saved-state files and locks remain native and unbound; fake transport replies alone cannot bind the behavior. A future binding must preserve the actual exported boundary and outside effects rather than introduce a check-only operation. No interpreter budget is authorized, no Runtime check ran and no report or prompt verdict is claimed. Native replay must exercise the real public boundary with temporary Git/state and synthetic transport, and separately prove the dispatch counts and original Check ceiling.
