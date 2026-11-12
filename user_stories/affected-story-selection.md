# Check every affected Story

As a PDD user, I want to check every Story affected by my change, so that I avoid paying to check known unrelated Stories.

Selection uses the existing saved-run base, or HEAD when no unique saved run exists. A committed no-run change with no working changes therefore checks all Stories. The proposed flag is explicit; ordinary `pdd test` still checks the full selection.

## Acceptance criteria

1. With changes that affect Stories A and B, `pdd test --affected` selects all their test variants and criteria, and sends no Check for known unrelated Story C.
2. When change scope, ownership or a required dependency relationship is uncertain, affected selection conservatively keeps all Stories that might be affected; with no established target it keeps the full inventory.
3. Ordinary full and named checks keep their current selection, cache, call limits and recovery behavior. Affected mode accepts no Story operands or `--lf`; rejected combinations have no execution effects.

## Rules to check

- Never omit a genuinely affected Story, a selected variant or a criterion. Unknown scope cannot establish independence. Global source/workspace/binding changes, changed safe-link targets and uncertain old/new owners require complete coverage or conservative fallback.
- Preserve full default checks and all required gates. No schedule, cap increase, failure waiver or automatic repair is included.

## Coverage boundary

```pdd-boundary
prompts/cli/runtime-check-plan.prompt.md
```

The Runtime scenario checks supplied planning/report facts only. Native cases must establish actual Git/source selection, CLI effects, saved-history admission and unchanged gates. Neither set has run for this draft.
AC3's Runtime case checks only default full selection. Cache, recovery, limits
and command rejection require the native cases; that partial check cannot prove
the complete criterion.
