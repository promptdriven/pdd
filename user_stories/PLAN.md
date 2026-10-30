# SVG layout spec

1. [Keep the built screen aligned with its drawing](svg-layout-spec.md): local prompt/drawing warnings and a failing browser comparison for missing layout parts.

## Product plans

1. [Choose a product path](product-map.md): read the durable map and the small one-run path.
2. [Track product progress](product-status.md): current, stale and not-run Stories by part and slice.
3. [Find the next product runs](product-next.md): ready runs and waiting needs.
4. [Start a planned run once](product-start.md): reuse its issue and optionally launch the feature workflow.

- [Compose a product Try](product-compose-try.md) — Runtime check: test/runtime/product-compose-try.json
- [Seed a journey](product-journey-seed.md) — Runtime check: test/runtime/product-journey-seed.json
- [Choose journey checks](product-choose-journeys.md) — Runtime check: test/runtime/product-choose-journeys.json
- [Coffee journey](journeys/J1-coffee-pickup.md) — Runtime check: test/runtime/J1-coffee-pickup.json
5. [Keep my prepared run issue](product-issue-binding.md): durable issue identity before search indexing.
6. [Reuse one product search](product-search-cache.md): one shared query and a short local snapshot across commands.
7. [Continue when my account lookup is unavailable](product-unavailable-actor.md): untrusted claims cannot break product commands.
8. [Repair one broken run link](product-repair-link.md): isolate a deleted link and relink it explicitly.
9. [Keep an uncertain run link](product-unresolved-link.md): retain unresolved hints without blocking other runs.
10. [Reuse my run link in another checkout](product-worktree-links.md): reuse compatible legacy state across worktrees.
11. [Keep my other saved run links](product-state-updates.md): preserve other bindings during coordinated updates.
