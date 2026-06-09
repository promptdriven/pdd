# Checkup Interactive Session Backend Spike

Issue: #1434
Parent: #1423
Decision date: 2026-06-09
Revised: 2026-06-08

## Decision

Use **Pi-first** backend for interactive prompt repair sessions:

- **Pi** owns the entire interactive workflow — QA, repair proposals, numbered menus, and user choices — when Node `>=22.19.0` and `@earendil-works/pi-coding-agent` are available.
- **Python** seeds the report, invokes the Pi bridge (`_pi_repair_bridge.js`), and reads the structured `approved_patches` output. Python applies patches and gates `--apply` in all cases.
- There is no separate Python TTY menu layer to develop. Pi's built-in interactive session replaces it entirely.

This unblocks #1423 implementation and eliminates the need to develop a custom Python TTY workflow.

## Pass Criteria

| Question | Result |
|----------|--------|
| Session state | **Pass** — Pi's `AgentSession` retains context across turns; Python reads structured output after the session ends. |
| Tool control | **Pass** — Pi bridge runs with `tools: ["read", "grep"]` plus one custom tool (`propose_repair_options`); `write`, `edit`, and `bash` are not enabled. |
| UX control | **Pass** — Pi drives the interactive session natively; Python only gates `--apply` and applies patches. |
| Packaging | **Conditional** — Pi requires Node `>=22.19.0` and `@earendil-works/pi-coding-agent`; `_pi_available()` guards the code path. |

## Backend Comparison

| Criterion | Pi-first (selected) | Hybrid (rejected) |
|-----------|---------------------|-------------------|
| Workflow development | Pi drives everything; no custom Python TTY to build | Python builds menus, validates choices, manages QA turns |
| Session state | Built-in `AgentSession` context retention | Split: Pi for QA, Python for choice state |
| Tool control | Explicit allowlist: `read`, `grep`, `propose_repair_options` | Same, but Python also manages a separate step loop |
| UX | Pi's native interactive session | Python `click.prompt()` + numbered menu code |
| Testability | Bridge subprocess mockable; `FakeInteractiveSession` covers Python layer | More Python paths to test |
| Packaging | Node `>=22.19.0` + npm; `_pi_available()` guard | Same guard, plus more Python code |

**Rationale for Pi-first over Hybrid**: The Hybrid design required building a Python TTY menu system in addition to the Pi integration — two workflows to maintain instead of one. Since Pi already provides an interactive session with tool-call support, the right boundary is: Pi owns the interaction, Python owns the patch application. No custom Python workflow is needed.

## Ownership Boundary

| Capability | Owner |
|------------|-------|
| Seed `pdd.prompt_source_set_report.v1` report | Python |
| Run interactive QA, propose repairs, render menus | Pi (via `_pi_repair_bridge.js`) |
| Record approved patches as structured JSON | Pi `propose_repair_options` custom tool |
| Read approved patches after session ends | Python |
| Enforce `--apply` before mutations | Python |
| Apply patches or rewrite prompt files | Python |
| Read-only repository inspection during session | Pi (`read`, `grep` tools) |

## Pi Bridge Shape

`pdd/_pi_repair_bridge.js` creates a Pi session with an explicit tool allowlist and a `propose_repair_options` custom tool. Pi drives the session; Python serialises input and reads output:

```js
// pdd/_pi_repair_bridge.js
const { createAgentSession, defineTool } = require("@earendil-works/pi-coding-agent");
const { Type } = require("typebox");

const proposeRepairOptions = defineTool({
  name: "propose_repair_options",
  label: "Record Repair Patches",
  description: "Record structured repair patches that the user has approved for a finding.",
  parameters: Type.Object({
    finding_id: Type.String(),
    patches: Type.Array(Type.Object({
      kind: Type.String(),
      target: Type.String(),
      anchor: Type.Record(Type.String(), Type.Unknown()),
      replacement: Type.String(),
    })),
  }),
  execute: async (_toolCallId, { finding_id, patches }) => {
    for (const p of patches) approvedPatches.push({ ...p, finding_id });
    return { content: [{ type: "text", text: `Recorded ${patches.length} patch(es).` }], details: {} };
  },
});

const session = await createAgentSession({
  tools: ["read", "grep"],
  customTools: [proposeRepairOptions],
});
await session.prompt(/* repair context */);
session.dispose();
// write approvedPatches → output.json
```

## Python Session Shape

Python invokes the bridge and reads the output — no menu or QA code required:

```python
# pdd/checkup_interactive_session.py  (PiInteractiveSession)
class PiInteractiveSession:
    def seed(self, report): self._report = report
    def run(self):
        # writes context.json, calls node _pi_repair_bridge.js, reads output.json
        ...
    def approved_patches(self): return [deepcopy(p) for p in self._patches]
```

## Packaging Notes

Pi is invoked through a Node.js bridge guarded by `_pi_available()`:

- Package: `@earendil-works/pi-coding-agent` (latest: 0.79.0)
- Node engine requirement: `>=22.19.0`
- TypeBox: imported from `"typebox"` (bundled with the package)
- Installation: `npm install --ignore-scripts @earendil-works/pi-coding-agent`

`_pi_available()` returns `False` when Node is absent or its major version is below 22. When `False`, callers should skip the Pi path or error with a clear message rather than attempting a Python TTY fallback (no fallback workflow is developed under this decision).

## Parent Issue Update

**Required external action before closing #1434:** Update parent issue #1423 with the following text:

> **Block 0 decision revised (#1434):** Use Pi-first backend for interactive prompt repair sessions.
>
> - Pi owns the entire interactive workflow (QA, proposals, menus) when Node `>=22.19.0` is available.
> - Python seeds the report, invokes `_pi_repair_bridge.js`, and applies the approved patches returned as structured JSON.
> - No separate Python TTY menu system is developed — Pi replaces it entirely.
>
> See `docs/checkup_interactive_session_spike.md` for the full decision record and ownership boundary.
