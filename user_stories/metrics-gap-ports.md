# Metrics capture gap fallback ports

I can record a fallback coverage-gap observation beneath the repository Git common directory and reject invalid inputs or unavailable storage.

```pdd-boundary
prompts/cli/metrics-gap.prompt.md
```

## Acceptance criteria

1. `recordCaptureGap` normalizes the repository slug to lowercase, formats the observation timestamp as ISO-8601 UTC, allocates a gap UUID, and writes only the `pdd.metrics.event.v1` incomplete-coverage record to `pdd/metrics-gaps/{id}.json` under `commonDir`.
2. `recordCaptureGap` raises `invalid-gap-observation` without touching storage or allocating a UUID when the repository slug, issue number, or timestamp is invalid.
3. `recordCaptureGap` raises `storage-unavailable` without writing a gap file when `commonDir` is missing or is a symbolic link.
