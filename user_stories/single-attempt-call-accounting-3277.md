# Keep single-attempt call counts disjoint

As a developer running `pdd test`, I want a single check attempt with uncertain calls to report confirmed known calls separately from unknown calls without double-counting, so that the reported known and unknown calls match the dispatched total.

## Acceptance criteria

1. When a single check attempt dispatches 34 provider calls with 33 known calls and 1 unknown call, `pdd test` reports `"calls": "unknown"`, `"known_calls": 33`, `"unknown_calls": 1` and `"accounting_complete": false` in JSON and `"33 AI calls + 1 unknown"` in the Prompt tests summary line.
2. When a single check attempt dispatches 34 provider calls with 1 unknown call and omits `"known_calls"`, `pdd test` subtracts the 1 unknown call from the 34 dispatched calls and reports `"calls": "unknown"`, `"known_calls": 33`, `"unknown_calls": 1` and `"accounting_complete": false`.
3. When a single check attempt completes with 3 calls, 2 known calls, 0 unknown calls and complete accounting, `pdd test` keeps `"calls": 3`, `"unknown_calls": 0` and `"accounting_complete": true`.

## What must not change

- Across replacement or capacity request IDs on a Story row, `pdd test` still sums each request ID's known and unknown components and keeps incomplete earlier observations incomplete.
- Complete receipts keep their numeric `calls` total, and positively unsent checks keep `0` AI calls.

## Rules to check

- On a single attempt, `provider_calls` and `calls` count total dispatched calls (`known_calls + unknown_calls`), not confirmed completed calls. Forbidden: clamping `known_calls` up to `provider_calls` or `calls` when `unknown_calls` is positive, or omitting subtraction of reported `unknown_calls` when `known_calls` is absent.
- Saved check recovery and lost-check cost calculation read the same disjoint `known_calls` value (`33` for `34` dispatched calls with `1` unknown call). Forbidden: persisting an inflated `known_calls` (`34`) in `batch.json` or `summary.json`.
- Multi-request restart replacement (`#3007`) continues to sum disjoint `known` and `unknown` components across distinct request IDs without letting a complete replacement erase an incomplete original attempt. Forbidden: dropping earlier attempt usage or double-counting within either attempt.
