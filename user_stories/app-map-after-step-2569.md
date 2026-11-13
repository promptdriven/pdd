# Refuse an invalid app-map after step before simulation

As a developer configuring an app map for `pdd simulate`, I want an invalid `after` step in `app-map.json` to refuse lint with its code, location and fix before simulation starts, so that I see how to write a nested `handler` step without an internal crash or a false lint pass.

## Acceptance criteria

1. When lint checks app-map.json alongside tests/walk/spike-world.json and refuses app-map.json with invalid-after-step at handlers[0].after[0], the lint outcome is "refused" with code "invalid-after-step", field "handlers[0].after[0]" and fix "Use exactly handler, input and bind for each step." even though tests/walk/spike-world.json passed.
2. When lint refuses app-map.json with invalid-after-step without a field pointer, the lint outcome is "refused" with code "invalid-after-step", field "app-map.json" and fix "Use exactly handler, input and bind for each step."
3. When both tests/walk/spike-world.json and app-map.json pass lint with matched supported capabilities, the lint outcome is "passed".

## What must not change

- A Story check or lint with no `app_maps` entry continues to decide admission from its reached prompts, per-test verdict and selected compatibility report.
- A passing `app-map.json` entry (`verdict: "passed"`) allows `pdd simulate` and `pdd lint` to proceed as usual.

## Rules to check

- Any applicable `app_maps` entry in a lint answer with `verdict: "refused"`, or an error problem or refusal targeting an applicable app map, must produce `state: "refused"` using the app map's specific error problem before any generic `lint-refused` job wrapper. Forbidden: `state: "passed"` when an applicable `app_maps` entry is refused or not checked.
- `pdd simulate` must initialize its lint warning list before recording diagnostics and route selected app-map lint refusals through app-map refusal output (`exit 4`, zero `/v1/try` requests). Forbidden: an unhandled `TypeError` (`exit 3`), a Story check table on Try setup refusal, or dispatching `/v1/try` after a refused app-map lint.

## Coverage boundary

```pdd-boundary
prompts/cli/runtime-outcome.prompt.md
```

The partial Runtime scenario checks pure lint outcome decisions on `prompts/cli/runtime-outcome.prompt.md` for refused app maps with and without `at` pointers and for a passing app-map control.
`pdd simulate` CLI exit code 4, lint-warning initialization, zero `/v1/try` dispatch, nested `"handler": {"prompt_path", "operation"}` refusal text in `src/runtime-client.mjs`, per-row `appMaps` scoping in `src/runtime-outcome.mjs`, and the complete valid `after` + `bind` example and `pdd lint` app-map validation scope note in `RUNBOOK.md` and `skills/pdd-prompting/RUNBOOK.md` are native-test and documentation obligations for PR 2; the partial Runtime check cannot prove CLI transport effects or documentation prose.
