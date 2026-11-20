# Human boundary card evidence provenance

As a reviewer approving a prompt or pull request, I want the Human Boundary Card to show owner lookup, local lint, hosted Story results, and native verification with their actual scope and source, so that partial checks or unreceipted claims never look like full proof.

## Acceptance criteria

1. When a review summary combines `pdd owner` resolving `prompts/alert-router.prompt.md`, `pdd lint --local` exiting with code 0 on SVG layout only, a hosted Story run passing 2 modeled policy assertions, and a native smoke test verified by a passing native receipt on "staging-east-1", the card shows all 4 observations with their actual source and scope in at most 25 lines.
2. When `pdd lint --local` exits with code 0 after checking SVG layout only, the card keeps the "partial" label and gives no credit for checking prompt rules, even when no warnings or problems occurred or no hosted Story run is present.
3. When a hosted Story run passes its modeled policy assertions on its loaded prompt, the card lists the modeled assertions it passed with its hosted source and loaded prompt scope, without crediting native target-host behavior or an unconnected owner.
4. Native smoke test behavior receives native credit only when backed by a passing native receipt that explicitly covers that behavior; claims with no receipt, a failed receipt, or a receipt covering a different behavior stay unverified with no native credit.

## Rules to check

- Zero exit from `pdd lint --local` is always partial. Forbidden: relabeling a local-only SVG layout lint run as passed or crediting it for checking prompt rules.
- Native behavior credit requires a passing native receipt covering that behavior. Forbidden: crediting unreceipted claims, failed receipts, or uncovered behaviors as native verified.
- Hosted Story runs check modeled policy assertions only. Forbidden: crediting a hosted run as native host verification or crediting an unconnected owning prompt.

```pdd-boundary
prompts/cli/human-boundary-card.prompt.md
```
