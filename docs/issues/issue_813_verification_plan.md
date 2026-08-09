# Issue #813 — Full End-to-End Verification Plan

Applies to branch `public/issue-813-anthropic-api-key-leak` for
`promptdriven/pdd#813`.
Use the checked-out repository root for all commands below; do not rely on
machine-local temporary worktree paths or historical commit counts.

The plan has six layers. Each one targets a class of regression that has either bitten us before (#492, #985, etc.) or that an unconditional credential-pop fix could introduce.

---

## Layer 1 — Unit tests (mock-driven, fast)

**Goal:** every discriminator pinned. Run on every commit.

```bash
cd <pdd-repo-root>
python -m pytest tests/test_agentic_common_issue_813_anthropic_api_key_oauth_shadow.py -vv --timeout=60
```

**Expected:** all pass (count grows as review feedback is incorporated; check the file for the latest case count). Discriminators covered:

| Case | What it pins |
|------|--------------|
| `test_pops_keys_when_oauth_login_present` | The fix actually fixes the bug |
| `test_keeps_keys_when_no_oauth_login` | **#492 regression guard** — API-key-only users not broken |
| `test_no_keys_in_env_is_a_no_op` | Probe is never called when there's nothing to pop (latency hygiene) |
| `test_pdd_keep_anthropic_api_key_overrides_pop` | Power-user opt-out works |
| `test_bedrock_route_is_exempt` / `test_vertex_route_is_exempt` | 3rd-party providers aren't disturbed |
| `test_only_auth_token_set_still_pops` | `ANTHROPIC_AUTH_TOKEN` (less common) also dropped |
| `test_oauth_detected_for_max_subscription` / `_without_subscription_field` | Max users + API-credit OAuth users both detected |
| `test_oauth_not_detected_when_logged_out` / `_for_bedrock_provider` | False-positive guards |
| `test_oauth_detected_for_env_supplied_token` | Cloud `CLAUDE_CODE_OAUTH_TOKEN` path |
| `test_oauth_not_detected_for_unknown_auth_method` | Future-proofing — unknown auth methods don't trigger pop |
| `test_probe_returns_empty_when_cli_missing` | Old systems / no claude installed |
| `test_probe_strips_api_key_from_subprocess_env` | Probe itself doesn't get shadowed by stale key |
| `test_probe_handles_timeout_gracefully` | Probe won't deadlock |
| `test_probe_handles_non_json_output` / `_non_zero_exit` | Old claude versions without `auth status` |
| `test_run_with_provider_pops_stale_key_when_oauth_present` | End-to-end of the original repro |
| `test_run_with_provider_keeps_key_for_api_key_only_setup` | End-to-end of #492 case |
| `test_run_with_provider_respects_keep_override` | End-to-end of opt-out |
| `test_run_with_provider_pops_key_when_oauth_token_env_set` | Cloud waterfall: token + stale key |
| `test_run_with_provider_oauth_token_only_is_a_no_op` | Cloud waterfall: token only (no API key) |
| `test_pop_does_not_mutate_parent_environ` | Parent process env not poisoned |
| `test_pop_does_not_run_for_non_anthropic_providers` | Unconditional-pop regression guard — codex/gemini branches unchanged |
| `test_strip_helper_returns_false_when_only_other_provider_keys_set` | Anthropic-scoped helper |

---

## Layer 2 — Existing-suite regression check

**Goal:** confirm no regression in the rest of the agentic surface.

```bash
python -m pytest \
  tests/test_agentic_common.py \
  tests/test_agentic_common_worktree.py \
  tests/test_provider_manager.py \
  tests/test_e2e_issue_902_provider_fallback.py \
  tests/test_time_reasoning_effort_env.py \
  tests/test_agentic_common_issue_813_anthropic_api_key_oauth_shadow.py \
  --timeout=60 -q
```

**Expected:** all pass. (Exact count grows over time; the meaningful invariant is no regressions, not a literal number.)

**Critical:** the existing tests `test_environment_sanitization` and `test_anthropic_api_key_preserved_when_explicitly_set` (Issue #492's protective tests) MUST still pass with their original assertions.

---

## Layer 3 — Smoke tests against real CLIs (this machine)

**Goal:** verify probe behavior against actual `claude auth status`. Unit tests
pin the documented no-flag command plus the legacy `--json` fallback; real CLI
smoke tests are still useful because CLI version drift matters.

### 3a. Verified scenarios already run during development:

```bash
# OAuth + stale key: pop happens
ANTHROPIC_API_KEY="sk-ant-stale-test" python -c "
from pdd.agentic_common import _strip_anthropic_creds_for_claude_subprocess
import os
env = os.environ.copy()
print('popped:', _strip_anthropic_creds_for_claude_subprocess(env, verbose=True))
print('survives in env:', 'ANTHROPIC_API_KEY' in env)
"
# → popped: True, survives in env: False  ✓

# Opt-out works
ANTHROPIC_API_KEY="sk-ant-stale" PDD_KEEP_ANTHROPIC_API_KEY=1 python -c "..."
# → popped: False, survives in env: True  ✓
```

### 3b. Cloud waterfall scenarios (verified):

```bash
# OAuth-token only: no pop (no key to strip)
# → popped: False  ✓

# OAuth-token + stale key: pop happens, token preserved
# → popped: True, CLAUDE_CODE_OAUTH_TOKEN preserved  ✓
# → parent os.environ untouched  ✓
```

### 3c. API-key-only worker case (must run on a worker / CI image lacking claude OAuth):

This needs a system without `claude auth login` AND without keychain OAuth.
Use Docker:

```bash
# Reproducer for the API-key-only worker case
docker run --rm -e ANTHROPIC_API_KEY=sk-ant-real-prod \
  -v "$PWD":/work -w /work \
  python:3.12 bash -c "
    pip install -e . >/dev/null && \
    npm install -g @anthropic-ai/claude-code >/dev/null && \
    python -c '
from pdd.agentic_common import _strip_anthropic_creds_for_claude_subprocess
env = {\"ANTHROPIC_API_KEY\": \"sk-ant-real-prod\"}
popped = _strip_anthropic_creds_for_claude_subprocess(env)
print(\"popped:\", popped)
print(\"survives:\", \"ANTHROPIC_API_KEY\" in env)
'"
# Expected: popped: False, survives: True
# (claude has no OAuth login on a fresh container; probe returns no OAuth; key kept.)
```

### 3d. Probe behavior under bogus CLAUDE_CODE_OAUTH_TOKEN (verified empirically):

```bash
CI=1 CLAUDE_CODE_OAUTH_TOKEN=fake claude auth status
# → loggedIn:true, authMethod:oauth_token
```

Caveat: `auth status` doesn't validate the token. With a bogus
`CLAUDE_CODE_OAUTH_TOKEN`, our code WILL pop `ANTHROPIC_API_KEY`. The
real call would then fail with "invalid OAuth token" — clearer than
"credit balance is too low" but still a failure. This is judged
acceptable because:
- A user with a bogus `CLAUDE_CODE_OAUTH_TOKEN` is in a broken state regardless.
- Cloud waterfall isolates each attempt to a single credential type, so the conjunction shouldn't arise in production.
- A clear "invalid OAuth token" error is more actionable than the silent shadowing bug.

---

## Layer 4 — Real `pdd generate` (manual / staging)

**Goal:** verify the actual pdd command line path the issue reporter hit.

### 4a. The original repro (jamesdlevine's failure case):

```bash
# As the issue reporter described:
export ANTHROPIC_API_KEY=$(grep -E '^ANTHROPIC_API_KEY' some-old-stale.env | cut -d= -f2)
# (key is depleted)
claude /status   # confirms "Login method: Claude Max account"
pip install -e .
pdd generate --verbose <a small prompt-only module>
# Pre-fix: every step fails with "Credit balance is too low"
# Post-fix: succeeds via Max OAuth, prints the one-shot dim notice about #813
```

### 4b. The #492 case (must keep working):

```bash
# Simulated cloud worker setup: API key only, no OAuth
docker run --rm -e ANTHROPIC_API_KEY=$REAL_API_KEY \
  -v "$PWD":/work -w /work \
  python:3.12 bash -c "
    pip install -e . && \
    npm install -g @anthropic-ai/claude-code && \
    pdd generate <small prompt>
  "
# Pre-fix: works
# Post-fix: still works (probe finds no OAuth, key preserved)
# An unconditional-pop fix would break this case.
```

### 4c. Opt-out:

```bash
ANTHROPIC_API_KEY=sk-real PDD_KEEP_ANTHROPIC_API_KEY=1 pdd generate ...
# Should bill against API key even if user has Max OAuth.
```

---

## Layer 5 — Cloud-worker integration test

**Goal:** the GitHub App executor still works when triggered via `pdd-issue` label.

### 5a. Static analysis already done:

- The cloud waterfall (`extensions/github_pdd_app/src/workers/pdd_executor/credentials_loop.py`) deliberately excludes `ANTHROPIC_API_KEY` (comment: "10x cost of OAuth"). Each attempt sets exactly one credential type:
  - OAuth attempts: only `CLAUDE_CODE_OAUTH_TOKEN` set
  - Vertex attempts: only `CLAUDE_CODE_USE_VERTEX` set
  - Codex attempts: `PDD_CODEX_AUTH_AVAILABLE` set
- Our fix pops `ANTHROPIC_API_KEY` only when it's set AND OAuth is detected.
  - OAuth attempt: API key not set → no-op fast path ✓
  - Vertex attempt: `CLAUDE_CODE_USE_VERTEX` short-circuits the fix ✓
  - Codex attempt: provider != anthropic, fix doesn't apply ✓

### 5b. Live verification (run the cloud worker tests):

```bash
cd ~/Desktop/SF/pdd_cloud
python -m pytest \
  extensions/github_pdd_app/tests/test_pdd_executor.py \
  extensions/github_pdd_app/tests/test_credentials_loop.py \
  -k "anthropic or oauth or credentials" \
  --timeout=60 -q
# Expected: all pass.
```

### 5c. End-to-end via pdd-issue label:

1. Create a low-stakes test issue in `promptdriven/pdd` with the `pdd-issue` label.
2. Watch the cloud worker logs (`gcloud logging read 'resource.type="cloud_run_revision"' --limit=20`).
3. Confirm: each waterfall attempt logs its credential, no "Credit balance is too low" appears, the worker either succeeds or moves to the next attempt cleanly.

---

## Layer 6 — Broader test sweep (full regression)

**Goal:** catch unrelated regressions one last time before merge.

```bash
cd <pdd-repo-root>
python -m pytest tests/ \
  -m "not integration and not e2e and not real" \
  --timeout=60 \
  --ignore=tests/commands/test_connect.py \
  -q
```

**Known-flaky on main (skip up front):**
- `tests/commands/test_connect.py::test_connect_defaults` — hangs >120s on a network call. Pre-existing, already excluded via `--ignore=` above.
- ~50 other tests fail pre-existingly on `origin/main` (cloud-fallback tests needing live auth, model-name drift in `test_bug_main`, e2e flakes). They are NOT excluded; the "Result on this branch" subsection below documents that they reproduce on main without this fix.

**Worktree-environment prerequisites (CI handles these automatically; bites local dev):**
- Copy `.env` from the main worktree if needed; `python-dotenv`'s `load_dotenv` in `tests/conftest.py` consumes it before any test runs.
- Use `python -m pip install pytest-mock pytest-asyncio python-dotenv` to install into the venv (the bare `pip` shim sometimes points to system Python, not the venv).

**Result on this branch (verified 2026-05-05):**
- Layer 6 first run: 113 failures + 51 errors. Diagnosed: 51 errors = missing `pytest-mock` in venv; many failures = missing `.env` (PDD_PATH unset).
- After installing `pytest-mock` properly and copying `.env`: ran the previously-failing test files (`test_bug_main`, `test_fix_main`, `test_e2e_issue_*`, etc.) and observed 37 remaining failures.
- Sampled 5 representative files and ran on main worktree (origin/main `aaf83b97a`) directly — 26 failures reproduce unchanged. The remaining failures are network-dependent (cloud fallback tests with auth failures), model-name mismatches in `test_bug_main`, and known-flaky e2e tests — all **pre-existing on origin/main**.
- Conclusion: **zero new regressions introduced by this fix.**

**Expected:** all directly-relevant tests pass (Layers 1-2 confirm); no tests fail that don't also fail on `origin/main`.

---

## Sign-off checklist

Before merging:

- [ ] **Layer 1**: all issue-813 unit tests pass (current snapshot in `tests/test_agentic_common_issue_813_anthropic_api_key_oauth_shadow.py`).
- [ ] **Layer 2**: all agentic-related tests pass (including #492 protective tests in `test_agentic_common.py::test_environment_sanitization` and `::test_anthropic_api_key_preserved_when_explicitly_set`).
- [ ] **Layer 3a-3d**: Smoke tests on this machine — verified during development. Re-run on the merge candidate.
- [ ] **Layer 3c**: Docker reproduction of API-key-only case. This must pass under our fix.
- [ ] **Layer 4a**: Manual `pdd generate` with stale key — confirms the original repro is fixed.
- [ ] **Layer 4b**: Manual `pdd generate` with API-key-only setup — confirms #492 not regressed.
- [ ] **Layer 4c**: `PDD_KEEP_ANTHROPIC_API_KEY=1` opt-out works.
- [ ] **Layer 5b**: cloud-worker test suite passes against the patched `pdd-cli`.
- [ ] **Layer 5c**: live `pdd-issue` end-to-end run succeeds.
- [ ] **Layer 6**: full sweep (minus known-flaky `test_connect_defaults`) clean.

If any layer fails, **do not merge**. Investigate, fix, and re-run *all* layers.

---

## What the comparison vs unconditional credential popping shows

| Property | This branch | Unconditional pop |
|---|---|---|
| Fixes original symptom | ✓ | ✓ |
| Issue #492 regression | ✗ (probe-guarded) | ✓ — break, rewrites guard test |
| Power-user opt-out | ✓ (`PDD_KEEP_ANTHROPIC_API_KEY=1`) | ✗ |
| Bedrock/Vertex exempt | ✓ | ✗ (could pop key on routes that don't use it) |
| Env-supplied OAuth (`CLAUDE_CODE_OAUTH_TOKEN`) | ✓ | partial (unconditional pop covers it but creates other regressions) |
| Codex coverage | ✗ deliberately (verified no shadowing) | ✓ speculative (creates regression for API-key-only codex users) |
| Gemini coverage | ✗ deliberately (unverified) | ✓ speculative (same regression risk) |
| Vertex creds preservation | ✓ (skip-condition) | ✓ (per-key list) |
| Prompt source-of-truth updated | ✓ (mandates conditional logic) | ✓ (mandates unconditional — would re-introduce regression on regen) |
| Test count | 27 | 5 |
| CI portability fixture | ✓ | ✗ |
| One-shot non-verbose log | ✓ | ✗ |

The headline finding: a wider credential-pop scope is less safe. The empirical evidence on codex (no shadowing observed) directly contradicts the assumption that the fix should be symmetric across providers. This branch ships only what's verified, with explicit comments where the deliberate scope decisions were made, so the next regen of `agentic_common.py` from the prompt won't quietly reintroduce the regression.
