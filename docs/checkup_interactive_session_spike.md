# Checkup Interactive Session Backend Spike

Issue: #1434
Parent: #1423
Decision date: 2026-06-09

## Scope of this PR

This change is **evidence and decision only** for Block 0 (#1434). It does not
ship production session code, CLI flags, patch application, or packaging
automation.

| In scope (#1434) | Out of scope (downstream issues) |
|------------------|----------------------------------|
| Backend decision record | `pdd/checkup_interactive_session.py` — #1435 |
| Pass-criteria evaluation | `_pi_repair_bridge.mjs` — #1435 |
| Ownership boundary table | `pdd checkup --interactive` — #1436 |
| Sample session artifact (JSON) | Deterministic patch apply — #1437 |
| Parent #1423 update text | Wheel `package-data` / npm install path — #1435 |

## Decision

Use a **Hybrid** backend for interactive prompt repair sessions:

- **Pi** may own contextual QA and repair proposal generation when the Pi runtime is available (Node `>=22.19.0` and `@earendil-works/pi-coding-agent` installed).
- **Python** owns deterministic menus, user choices, `--apply` gating, session persistence, and any future file mutation — in all cases.
- **Python TTY** remains the fallback backend when Node/Pi is unavailable or unsuitable for CI/headless execution.

This unblocks #1423 implementation while keeping destructive control in Python.

## Pass Criteria

| Question | Result |
|----------|--------|
| Session state | **Pass** — persist finding IDs, proposals, user questions, answers, and choices in structured session state. |
| Tool control | **Pass (with explicit allowlist)** — Pi runs with `tools: ["read", "grep", "propose_repair_options"]` only; `write`, `edit`, and `bash` are not enabled. |
| UX control | **Pass** — Python renders numbered `[1]` through `[4]` menus, validates choices, and gates `--apply`. |
| Packaging | **Conditional** — Pi requires Node `>=22.19.0` and the `@earendil-works/pi-coding-agent` npm package; Python TTY has no new runtime dependency. |

## Backend Comparison

| Criterion | Pi AgentSession | Python TTY | Hybrid |
|-----------|----------------|------------|--------|
| Session state | Built-in via JSONL/in-memory `SessionManager` | In-memory list + JSON file | Hybrid: Pi for conversational context; Python for choice/apply state |
| Tool control | Explicit allowlist required (defaults include `write`/`edit`/`bash`) | No LLM tools by default | Pi allowlist applied; Python never delegates apply |
| UX / menu control | LLM can output free text; menus must be enforced by caller | `click.prompt()` + `click.Choice()` is deterministic | Python always owns menu rendering and choice validation |
| Latency | Warm session amortizes turns; cold start adds Node startup time | One `llm_invoke` call per turn; no Node startup | Pi warmup on first turn; subsequent turns are fast |
| Testability | In-memory `SessionManager` supports unit tests; custom tools mockable | Simplest to test; standard Python mocking applies | Pi path testable via `SessionManager.inMemory()`; Python path fully unit-testable |
| Packaging | Node `>=22.19.0` + npm (`@earendil-works/pi-coding-agent@0.78.1`) | Python only; existing `click` and `llm_invoke` dependencies | Requires Node guard; falls back to Python TTY when unavailable |
| CI / headless | Must guard `node --version`; Pi TUI must not be invoked | Works everywhere Python does | Guard added; CI exercises Python TTY path |

**Rationale for Hybrid**: Pi provides superior session continuity and structured custom tool support, but the Node `>=22.19.0` requirement is a real packaging constraint for a Python CLI, and [#1423](https://github.com/promptdriven/pdd/issues/1423) requires Python-owned numbered menus and choice validation. The Hybrid decision captures Pi's QA/proposal benefits when the runtime is available while ensuring Python TTY covers all CI, headless, and restricted-environment cases. Destructive control (apply gating, file mutation) stays in Python regardless of which QA engine is active.

**Rejected: Pi-first** — Would assign menus and user choices to Pi (#1434 spike doc draft), conflicting with #1423's interaction policy. Also makes the primary backend unavailable on normal Python installs without a documented npm packaging path.

## Ownership Boundary

| Capability | Owner |
|------------|-------|
| Seed `pdd.prompt_source_set_report.v1` report | Python |
| Persist session state and selected choices | Python |
| Render numbered `[1]...[4]` repair menus | Python |
| Validate user menu input | Python |
| Enforce `--apply` before mutations | Python |
| Apply patches or rewrite prompt files | Python |
| Conversational QA over retained context | Pi when available; Python TTY fallback otherwise |
| Generate structured repair proposals | Pi `propose_repair_options` when available; Python TTY fallback otherwise |
| Read-only repository inspection | Pi may use `read`/`grep`; Python remains responsible for policy |

## Pi Prototype Shape

Pi session configuration must use an explicit tool allowlist. Do **not** rely on Pi defaults (which include `write`, `edit`, and `bash`):

```ts
import { createAgentSession, defineTool } from "@earendil-works/pi-coding-agent";
import { Type } from "@sinclair/typebox";

const proposeRepairOptions = defineTool({
  name: "propose_repair_options",
  description: "Return structured repair proposals for a finding",
  parameters: Type.Object({
    finding_id: Type.String(),
    proposals: Type.Array(Type.Object({
      proposal_id: Type.String(),
      label: Type.String(),
      rationale: Type.String(),
      tradeoff: Type.String(),
      recommended: Type.Optional(Type.Boolean()),
    })),
  }),
  execute: async (params) => params,
});

const session = await createAgentSession({
  tools: ["read", "grep", "propose_repair_options"],
  customTools: [proposeRepairOptions],
});
```

## Python TTY Prototype Shape

The Python fallback keeps an in-memory or JSON-backed session list and performs one `llm_invoke` call per QA/proposal turn. It stores the same fields as the Pi path so later #1423 work can share a backend-neutral session contract:

```python
from pdd.llm_invoke import llm_invoke

def run_tty_session(report, turns=3):
    history = []
    for _ in range(turns):
        user_input = click.prompt("[repair]")
        history.append({"role": "user", "content": user_input})
        response = llm_invoke(messages=history, ...)
        history.append({"role": "assistant", "content": response})
    return history
```

## Packaging Notes

Pi packaging is acceptable only behind a runtime guard **and** a documented install
path. At spike time the Python wheel has **no** root `package.json` that installs
`@earendil-works/pi-coding-agent`; `_pi_available()` can only succeed when the
user has already installed the npm package in their environment. That is why this
spike selects **Hybrid** (not Pi-first): Pi is an optional QA/proposal engine,
while Python TTY is the guaranteed primary path for normal installs, CI, and
headless runs. Automating the npm install story is deferred to #1435.

Researched package at time of spike:

- Package: `@earendil-works/pi-coding-agent@0.78.1`
- Node engine requirement: `>=22.19.0`
- Manual install (not automated in this PR): `npm install --ignore-scripts @earendil-works/pi-coding-agent`

Guard pattern (pseudocode for #1435):

```python
import shutil, subprocess

def _pi_available() -> bool:
    if shutil.which("node") is None:
        return False
    try:
        out = subprocess.check_output(["node", "--version"], text=True).strip()
        major = int(out.lstrip("v").split(".")[0])
        return major >= 22
    except Exception:
        return False
```

CI and headless runs must exercise the Python TTY path when `_pi_available()` returns `False`.

## Sample Session Artifact

See `docs/checkup_interactive_session_tty_sample.json` for a sanitized **Python
TTY** session artifact that demonstrates the Hybrid decision. The artifact uses
`backend: "python_tty"` and `decision: "hybrid"` because Python owns menus,
choice validation, and `--apply` gating in all cases; Pi is not invoked in this
sample. It covers:

1. Seeded `pdd.prompt_source_set_report.v1` finding.
2. Three retained-context QA turns: "why?", "what check failed?", and "tradeoff?".
3. Structured repair proposals (P-001 Adopt Pi, P-002 Custom TTY, P-003 Hybrid recommended).
4. Python-rendered `[1]...[4]` numbered menu with selected choice and `apply: false` gating.
5. An `ownership` block listing Pi vs Python responsibilities under Hybrid.

## Parent Issue Update

**Required external action before closing #1434:** Update parent issue #1423 with the following text:

> **Block 0 decision recorded (#1434):** Use a Hybrid backend for interactive prompt repair sessions.
>
> - Pi owns contextual QA and proposal generation when Node `>=22.19.0` is available.
> - Python owns deterministic menus, choice validation, `--apply` gating, session persistence, and file mutation — in all cases.
> - Python TTY is the fallback when Node/Pi is unavailable (CI, headless, restricted environments).
>
> See `docs/checkup_interactive_session_spike.md` for the full decision record, backend comparison table, and ownership boundary.
