# PDD documentation

Start with the [README](../README.md).

- [The `/pdd` skill](../skills/pdd/SKILL.md): single-entry workflow router (`product`, `bug`, `feature`, `small-change`) and co-located guides:
  - [Prompting guide](../skills/pdd/references/prompting.md): module ownership, top-of-file headers, 100% Truth, and brownfield PRs.
  - [Story guide](../skills/pdd/references/stories.md): Stories, compact scenario JSON, targets, operators, and schemas.
  - [Product roadmaps](../skills/pdd/references/product.md): multi-part maps, plans, contracts, and `kind: native-only` specs.
  - [Ports and CLI](../skills/pdd/references/ports-and-cli.md): external fakes, 3-Port Adoption Rule, CLI programs, and `pdd mcp`.
  - [UI and screens](../skills/pdd/references/ui-and-screens.md): single-file plain-prose UI, optional `app-map.json`, `.ui.svg`, and `pdd sim`.
  - [Verification](../skills/pdd/references/verification.md): native tests, bug TDD, Feature Maps (`verify.paths`), Deliberate-Break Probe, and `pdd prove`.
- [Build a whole product](build-a-whole-product.md): map a product and plan its runs.
- [Usage guide](USAGE.md): install, setup, `pdd init`, `pdd status`, runs, gates, checks on the PDD interpreter, clean up, and fixes.
- [Workflows in depth](workflows.md): interactive `/pdd` modes, headless `pdd autopilot`, product plans, and skill locations.
- [Interpreter boundaries](runtime-boundaries.md): offline review, server lint, native factory bindings, and call-accounting evidence.
- [CLI reference](cli.md): every command, and how to run from a source checkout.
- [Refactor runbook](refactor-runbook.md): separate structural cleanup from behavior changes and prevent pattern drift.
- [Report a problem](ISSUES.md): how you or your agent files a clear issue about pdd.
