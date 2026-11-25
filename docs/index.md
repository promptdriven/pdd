# PDD documentation

Start with the [README](../README.md).

- [The `/pdd` skill](../skills/pdd/SKILL.md): single-entry workflow router (`product`, `bug`, `feature`, `small-change`) and co-located guides:
  - [Prompting guide](../skills/pdd/references/prompting.md): module ownership, `// Prompt:` headers, 100% Truth, `kind: native-only` specs, and approvals.
  - [Story guide](../skills/pdd/references/stories.md): Stories, compact scenario JSON, targets, operators, and schemas.
  - [Product roadmaps](../skills/pdd/references/product.md): multi-part maps, plans, contracts, and `--through prompt-pr`.
  - [Ports and CLI](../skills/pdd/references/ports-and-cli.md): external fakes, 3-Port Adoption Rule, CLI programs, and `pdd mcp`.
  - [UI and screens](../skills/pdd/references/ui-and-screens.md): single-file plain-prose UI, optional `app-map.json`, `.ui.svg`, and running UI prompts directly with `pdd`.
  - [Verification](../skills/pdd/references/verification.md): real-path tests, Feature Maps (`verify.paths`), Deliberate-Break Probe, and `pdd prove`.
  - [Formal verification](../skills/pdd/references/formal.md): 3-tier code-bound stack, Z3 isolation, mutation control, and Rule Coverage reporting.
- [Usage guide](USAGE.md): install, `pdd setup`, `pdd init`, `pdd status`, interactive `/pdd`, Autopilot, interpreter checks, the Prompt Interpreter, and fixes.
- [Workflows in depth](workflows.md): interactive `/pdd` modes, headless `pdd autopilot`, product plans, and skill locations.
- [Build a whole product](build-a-whole-product.md): map a multi-part product, contracts, waves, and planned runs.
- [CLI reference](cli.md): every command form, option, and running from a source checkout.
- [Metrics](metrics.md): local Autopilot throughput, funnel, and 7-day cohort metrics (`pdd metrics`).
- [Autopilot factory & smoke tests](autopilot-factory.md): offline Autopilot factory harness and fresh release smoke sandbox.
- [Autopilot issue refinement](autopilot-issue-refinement.md): how active intake strengthens a weak issue, and how to write an issue that is ready at the first check.
- [Interpreter boundaries](runtime-boundaries.md): offline review, server lint, native factory bindings, and call-accounting evidence.
- [Interpreter capacity & retries](lint-capacity.md): remote lint wait queues, slot limits (`PDD_MAX_JOBS`), and retry behavior.
- [Runtime bindings](runtime-bindings.md) & [Runtime interface admission](runtime-interface-admission.md): resource binding resolution and hosted interface admission rules.
- [Prompt re-entry verification](prompt-reentry-verification.md): verifying edits to prompts and code ownership parity.
- [Report a problem](ISSUES.md): how you or your agent files a clear issue about pdd.
