# Compare rendered screens against reference drawings through Runtime ports

I can compare rendered page geometry against a `.ui.svg` reference drawing and format the comparison report through declared file and browser ports.

```pdd-boundary
prompts/cli/screen-compare.prompt.md
```

## Acceptance criteria

1. Comparing a rendered page whose visible ids, labels, regions and spatial order match its `.ui.svg` reference passes every required row.
2. Comparing a rendered page with a misplaced region and a missing scoped label reports `region` and `missing` rows and sets `passed` to false.
3. Unsafe `.ui.svg` reference markup fails with `unsafe-reference-svg`, and an invalid comparison report fails formatting with `invalid-comparison-report`.
4. Formatting a comparison report produces a Markdown `Screen vs drawing` table that escapes special characters in labels.
