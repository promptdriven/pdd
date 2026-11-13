# Refuse lint when a declared app map is refused

As a prompt author running `pdd lint`, `pdd test` or `pdd simulate`, I want a refused app map declared for my Story or simulation to refuse that lint gate, so that a broken app map never looks like a clean pass or starts paid AI calls.

The four acceptance criteria were approved in chat.

## Acceptance criteria

1. When a Story's test declares an app map in `app_maps` and the interpreter refuses that map during lint, `pdd lint` exits with code 4, reports `refused` with the map's problem code, reason and fix, and reports 0 passing tests for that Story.
2. When a Story's test declares a refused app map in `app_maps`, `pdd test` exits with code 4, sends 0 check requests and spends 0 AI calls, and `pdd test --read` on that saved lint or check batch preserves `refused` with exit code 4.
3. When a Story's test declares a refused app map in `app_maps` or `pdd simulate` selects a refused app map, `pdd simulate` sends 0 Try requests and spends 0 AI calls (exit code 4 in page mode, exit code 125 in `--cli` and `--serve` door modes), and an unrelated scoped-out lint refusal prints `Lint diagnostic:` on stderr without throwing.
4. When the interpreter reports `app_maps` verdicts and a selected app map is `not-checked` or missing its verdict, `pdd lint`, `pdd test` and `pdd simulate` report `not run` with exit code 5 and 0 AI calls; a Story that does not select a refused app map keeps its own passing lint result.

## Rules to check

- A test or simulation passes lint only when its test verdict passes and every app map selected by that scenario (`app_maps`) or simulation (`appMap`) passes when `app_maps` verdicts are reported, with no non-warning refusal or problem naming any selected map. Forbidden: `pdd lint` exiting 0 (`passed`), `pdd test` posting `/v1/check`, or `pdd simulate` posting `/v1/try` when a selected app map is refused.
- Specific map problem records (`code`, `file`, `at`, `reason`, `fix`) win over the interpreter's generic `lint-refused` summary record, including when an earlier test refusal occupies `result.refusals`. Forbidden: dropping the map's specific error code or masking a second refused app map behind an earlier test refusal.
- Unrelated app-map refusals stay scoped: a Story that declares no refused app map keeps its own passing verdict and surfaces the unselected refusal as a `Lint diagnostic:` warning without throwing on missing warning storage. Forbidden: refusing an unrelated Story or throwing a runtime `TypeError` in `pdd simulate`.

## Evidence and check limits

`prompts/cli/runtime-outcome.prompt.md` and `prompts/cli/runtime-client.prompt.md` own per-selection lint outcomes and the shared lint gate; neither prompt declares a Runtime interface block, so `pdd test` cannot run against them directly (`Runtime prompt check: Not run`). Verification uses native public-boundary and bounded-domain formal tests in PR 2 plus live zero-AI-call hosted lint checks.

[Proposed synthetic native cases](../test/runtime-admission/declared-app-map-lint-cases.json).
