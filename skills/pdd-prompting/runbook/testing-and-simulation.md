# Runbook: Running pdd test, pdd simulate, and Troubleshooting

> Deep reference for [RUNBOOK.md](../RUNBOOK.md).

## 11. `pdd test`

- Run `pdd test [STORY...]` (already runs lint first—never run `pdd lint` right before `pdd test`). Useful flags: `--files` (offline upload list), `--json`, `--read BATCH` (resume saved batch without resending), `--max-calls N`, `--target code` (execute CLI scenarios against native code, 0 AI calls).
- **Common refusals (0 AI calls):**
  - `story-criterion-mismatch`: criterion text in explicit `criteria` drifted from `user_stories/<slug>.md`—omit `criteria` in Short JSON or run `pdd lint --bind-criteria <story>`.
  - `graph-schema-type-list` / `invalid-schema`: fix `["string", "null"]` → `{"oneOf": [...]}` or missing `additionalProperties: false` (§3).
  - `scenario-integer-out-of-range`: use `n.toExponential()` for JS Number values outside `±(2^53-1)` (§3).
  - `invalid-context`: `context` rows must have exact keys `{"prompt_path", "paths"}` (`<= 16` files, `<= 120 KiB`).
  - `value-differs` / `✗`: inspect the report link; fix the prompt if the prompt is wrong, or ask the person before changing any expected value (§4).

## 12. `pdd simulate` and Save as test

- Start interactive Simulator: `pdd simulate <story> --new` (`--new` uploads changed prompts or `app-map.json`; add `--app-map PATH` for a non-default map, `--cli` for CLI shell, `--serve` for local HTTP).
- Never launch an interactive Simulator session unless the person asks; offer the command in text.
- **Save as test:** in the Simulator UI, saved transcripts export a draft scenario; review expected values with the person (§4) before keeping them.

## 16. Known limits today

- Server step timeout: `10` minutes per step; keep each step to `1` action or `<= 10` moves/rows/calls.
- Upload cap: `10 MiB` and `10,000` Git-visible files.
- Plain JSON integer literals outside `±(2^53-1)` are refused unless written in exact JS Number spelling (BigInt-only checks belong in §17 native vector tests).
- Screen HTML strips `<script>` and inline event handlers; use `app-map.json` handlers and `timers` (§13, §20).

## 19. Use a simulation from your terminal or curl

- Run `pdd simulate <story> --serve --new` to expose a local Try endpoint, then `curl -sS -X POST http://127.0.0.1:<port>/call -H 'content-type: application/json' -d '{"operation":"...","input":{...}}'` to test individual operations interactively.
