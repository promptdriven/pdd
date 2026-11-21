# Runbook: Running pdd test, pdd simulate, and Troubleshooting

> Deep reference for [RUNBOOK.md](../RUNBOOK.md).

## 11. `pdd test`

- Run `pdd test [STORY...]` (already includes whole-program interpreter lint—never run `pdd lint` right before `pdd test`; native Short JSON scenarios run directly without expanding to `v1` on disk). Reuse unchanged passes from `.pdd/cache/test/`; flags: `--lf` (last failures), `--cache-clear`, `--retry BATCH` (confirmed unstarted checks only), `--read BATCH [--details]` (resume saved batch without resending; `--details` prints full step diagnostics), `--files` (offline upload manifest), `--json`, `--max-calls N`, `--timeout MIN`, `--target code` (run CLI scenarios against native code, 0 AI calls).
- **Live progress, waiting & maintenance:** `pdd test` streams live SSE phase updates (`queued` → `lazy_interfaces` → `step 1/N` → `done`) and `pdd test` / `pdd test --read BATCH` wait until every Story ends (printing `Still running: …` if no SSE event arrives). During announced maintenance (`pdd waits, then continues`), let `pdd` wait—no Ctrl-C, no `timeout` wrapper, and no short `--timeout`. (An Autopilot core job follows §15 "Autopilot core jobs" instead.)
- **Exit codes:**
  - `0` passed: put the one-line result in the PR (§15). A `DRAFT` pass is not an approval.
  - `1` failed: inspect `Why:`, `Next:`, `Rerun:`, and the report's "Debug this step". Fix only what evidence proves; a person decides expected values. At most **2 fix rounds** for the same `✗`, then stop and tell the person what you tried.
  - `2` command error: wrong option or Story name (`pdd test --help`).
  - `3` unknown or still running: run `pdd test --read BATCH` once with a long shell timeout; never resend the check.
  - `4` refused (`no verdict ·`): nothing was judged—either a file breaks a rule (fix that file, table below) or the AI service failed (change no file; never resend on your own).
  - `5` not run: sign-in, network, server busy, or capacity (`gh auth status`, wait, or tell the person).
- **`Rerun:` stability verdicts** (total AI calls already include reruns—never add the rerun share twice):
  - `Rerun: failed 3 of 3 (stable).` → failure repeats consistently; rechecking unchanged files will not help.
  - `Rerun: failed 1 of 3 (unstable).` → answers varied; make the rule in the prompt firmer (do not fit to one answer).
  - `Rerun: passed M of M reruns.` → reruns passed, but the original failed check still needs investigation.
  - `Rerun: skipped (<reason>).` → no stability verdict (nor does a single run or refusal supply one).
- **No verdict & "A failed check is a FAIL":** one step with no answer (e.g. `graph-provider-failure`, `graph-uncertain-child-dispatch`) makes its Story `no verdict` (exit 3, 4, or 5), **but other steps can still fail**. When passed checks < total (`no verdict · 10 of 13 criteria · 17/19 checks`), inspect the report: any step showing `expected X, got Y` is a **FAIL**, never `not run`. For pure `no verdict` / `busy ·` with an AI-service or limit cause, tell the person with `pdd`'s next step, change no file, and **never resend on your own**.
- **Common refusals & whole-program lint diagnostics (0 AI calls):**
  - `shared-port-signature-mismatch` (error): two prompts call the same `<port>.<op>` with incompatible input or output shapes—align both prompts' port prose or split into distinct `<port>.<op>` names.
  - `mocked-port-owner-mismatch` (error): a scenario mocks a port owned by a peer prompt (or mocks an undeclared port)—call the peer prompt directly or fix the port name.
  - `contract-schema-mismatch` (error): a prompt's input/output contract disagrees with a linked `contracts/*.json` or `contracts/*.md` schema—reconcile the prompt and contract.
  - `unwired-cross-cutting-operation` (advisory warning): an exported cross-cutting operation (e.g. auth/audit/policy hook) is declared in the program graph but never called by any entry or peer—wire the call or confirm it is intentionally standalone.
  - `story-criterion-mismatch`: omit `criteria` in native Short JSON to auto-bind Story lines directly. If explicit criterion text already matches `user_stories/<slug>.md` word-for-word under legacy IDs (`AC1..ACN`), bind on disk with `pdd lint --bind-criteria <story>`. If criterion text drifted from the Story or an `ac-sha256-...` ID is stale, `--bind-criteria` refuses with exit 4—review the Story and update the test (or ask the person if expected behavior changed).
  - `graph-schema-type-list` / `invalid-schema`: fix `["string", "null"]` → `{"oneOf": [...]}` or missing `additionalProperties: false` (§3).
  - `scenario-integer-out-of-range`: use `n.toExponential()` for JS Number values outside `±(2^53-1)` (§3).
  - `invalid-context`: `context` rows must have exact keys `{"prompt_path", "paths"}` (`<= 16` files, `<= 120 KiB`).
  - `unchecked-criteria`: every criterion needs at least one exact check.
  - `run-admission-failed` / `repository-graph-catalog-error`: raise `--max-calls` (up to `1000`) or lower `max_calls` in prompt `calls`.
  - `unknown-simulation-operation` / `port-operation-kind-or-access`: bind only operations declared for the invoked entry and keep one resource family per `<port>.*` prefix (§5, §21).

## 12. `pdd simulate` and Save as test

- Start interactive Simulator: `pdd simulate [STORY|PROMPT.md] [--new] [--fresh]` (e.g. `pdd simulate prompts/<app>.prompt.md` opens a single-file plain-prose UI directly on the Screen tab without a Story or `app-map.json`; `--new` uploads changed prompts or `app-map.json`; `--fresh` bypasses saved answer caches for a clean LLM pass; `--app-map PATH` loads a non-default map; `--no-open` skips opening a browser; `--cli` starts the CLI shell; `--serve [PORT]` starts local HTTP; `--stop [STORY|PROMPT.md]` stops a running simulation). Never launch an interactive Simulator session unless the person asks.
- **Link privacy (security rule):** show the Simulator link only to the person. **Never write it into a file, PR, issue, or shared channel**—anyone with the link can use it. Keep private `--agent NAME` owner chat links out of shared messages.
- **Save as test (boundary rule):** **only the person saves a case. Never save one yourself.** After the person says they saved cases, run `pdd simulate <story>` again to pull them into the Story's test file (`added to tests/<file> as step <id>`), verify every criterion still has an exact check, and review expected values with the person (§4).

## 16. Known limits today

- Server step timeout: `10` minutes per step; keep each step to `1` action or `<= 10` moves/rows/calls.
- Upload cap: `10 MiB` and `10,000` Git-visible files; appearance-context reads at most 4 views (`64 KiB` total SVG bytes; mockup selector cap `256 KiB` per SVG).
- Report previews drop line breaks (`"Hi"` vs `"Hi\n"`) and clip strings at 256 chars (`…`), while checks compare exact full values.
- Plain JSON integer literals outside `±(2^53-1)` are refused unless written in exact JS Number spelling (BigInt-only checks belong in §17 native vector tests).
- Screen HTML preserves sanitized inline `<style>` and declarative `data-pdd-op` controls while stripping `<script>`, `<iframe>`, and inline `on*=` handlers; use `handle_event`, optional compact `app-map.json` handlers, and host `timers` (§13, §20).

## 19. Use a simulation from your terminal or curl

- **CLI door:** `pdd simulate <story> --cli` prints a shim `PATH` line (`--shell` opens bash/zsh with it); `pdd simulate --save-last` appends the last command and observed result to the Story's test file for review.
- **HTTP door:** `pdd simulate <story> --serve 8080` binds loopback `http://127.0.0.1:8080` and serves Screen resources plus named HTTP routes declared via each entry's `input_schema.title` (e.g. `"title": "HTTP GET /api/books"`, supporting literal segments and `:id` params; unknown routes return `404` with 0 AI calls). Return `{status, headers?, body}` and exercise declared routes with `curl` or `fetch`.
