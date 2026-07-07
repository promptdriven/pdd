# Codex CLI pin record (design §10 still-to-confirm #1–#3)

Everything below was verified **without a provider account, without a real
API key, and without network egress** — the probe's scripted upstream and the
recording proxy are the only reachable HTTP destinations (loopback), the API
key is a fake local marker string, and the §8.1.1 egress guard black-holes
everything else. Zero model tokens were spent.

## Pinned build

| Field | Value |
|---|---|
| CLI version (`codex --version`) | `codex-cli 0.142.4` |
| Version command | `["codex", "--version"]` |
| Verified on | 2026-07-07, macOS (Homebrew install, `/opt/homebrew/bin/codex`) |
| Wire API | **Responses only** — `wire_api = "chat"` is rejected by this build |
| Sampling seed | **Not exposed** (no `seed`/`temperature` flag in `codex exec --help`) → §6.5's fallback applies: N=5 unseeded trials per cell |

## How each §10 item was confirmed

Run the probe yourself (still zero-billing):

```bash
cd research/repo-bloat-benchmark
python3 -m harness.runner.codex_probe --json verdict.json     # CLI form
RB_CODEX_PROBE=1 python3 -m pytest harness/runner/tests/test_codex_probe.py  # pytest form
```

The probe builds a real §8.1.1 `FrozenEnvironment` (fresh `CODEX_HOME`,
generated config, sanitized env, egress guard), starts the recording proxy in
front of a **scripted two-turn Responses-API upstream**, and runs
`codex exec --strict-config` against it. The scripted "model" orders one
`exec_command` (`ls`); the follow-up request must echo a marker file that
exists only in the probe workdir. Verdict on the pinned build — all checks
PASS:

| Check | Meaning |
|---|---|
| `config_strict_ok` | generated config parses under `--strict-config` (all key names valid for this build) |
| `routed_all_traffic` | every provider request hit the configured `base_url`; proxy record count == upstream request count; all paths `/v1/responses` → **§10 #3 confirmed** |
| `proxy_byte_exact` | archived payloads byte-identical to what the upstream received |
| `usage_captured` | provider `usage` parsed per request out of the Responses SSE stream → token-level penetration metrics + H2 trajectory family are **supported** |
| `auth_via_env_key` | `Authorization: Bearer <env_key var>` populated from the provider `env_key` |
| `web_search_tool_absent` | `web_search = "disabled"` removes the tool from the request tool list |
| `local_exec_observed` | the marker file was echoed back in turn 2 → the CLI executed `ls` **locally** (PTY `exec_command`) → **§10 #2: local shell execution, kernel-visible; no server-side retrieval tool is offered** (tool list: `exec_command`, `write_stdin`, `update_plan`, `request_user_input`, `view_image`, `multi_agent_v1`, `get_goal`/`create_goal`/`update_goal`) |
| `session_log_archived` | rollout `sessions/**.jsonl` written into the ephemeral home and archived → session-parser bypass cross-check has its input |
| `no_stray_requests` | no non-POST/off-path traffic reached the upstream |

## Config-key facts validated with `--strict-config` (this build)

- `wire_api = "chat"` → **rejected** ("no longer supported"); use
  `wire_api = "responses"`. Consequence: the recording proxy and all
  calibration fixtures must handle Responses-shaped SSE (they do — see
  `harness/context_snapshots/proxy.py::_analyze_response_body`).
- `web_search` (top-level) takes a **string**; `web_search = "disabled"`
  removes the `web_search` tool from requests. `[tools] web_search =
  true|false` parses but does **not** change tool presence (inert for our
  purpose) — do not use it.
- `[model_providers.<id>] env_key = "OPENAI_API_KEY"` is honored: the value
  of that env var is sent as the Bearer token.
- `model_context_window = <int>` is recognized; `model_max_output_tokens` is
  **not** a valid field in this build.
- With a **custom model provider, model metadata is missing for every model
  id** ("Defaulting to fallback metadata" warning). The context window that
  drives client-side compaction therefore MUST be registered explicitly via
  `model_context_window` in the frozen config (now a `FreezeConfig` field,
  covered by the env fingerprint). The warning itself persists and is
  cosmetic once the window is registered.

## What still requires a human pre-registration decision

The **mechanics** above are confirmed; the following **values** must be
chosen and frozen by the experimenters before pilot runs (they change the
env fingerprint, so the choice is self-documenting):

1. Final `model_id` (probe used `gpt-5.1-codex-max` as a placeholder — any
   id works mechanically against the proxy; the real run needs the id the
   provider account actually serves).
2. Final `reasoning_effort` (probe: `medium`).
3. The `model_context_window` value matching the chosen model.

## What this record does NOT cover (needs a live provider — billing)

- Confirming the chosen `model_id` is served by the real provider account,
  and that real-provider responses stream the same event shapes the scripted
  upstream emits (they follow the published Responses API; the calibration
  gate re-checks proxy fidelity on the first real run before any pilot cell).
- Kernel-level egress lockdown (Linux container tier) remains open — the
  proxy-var guard is portable but not kernel enforcement (design §8.1.1).
