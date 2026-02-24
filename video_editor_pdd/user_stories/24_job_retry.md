# User Story 24: Job Retry

**As a** director,
**I want to** retry any failed pipeline job without re-running upstream stages,
**So that** transient failures don't force me to restart the entire pipeline from scratch.

## Acceptance Criteria

- [ ] Failed jobs show a [Retry] button in the SSE log panel and in the pipeline status sidebar
- [ ] `POST /api/jobs/:id/retry` creates a new job with the same parameters as the original and returns a new `{ jobId }`
- [ ] Retry does not re-run upstream stages — it reuses existing upstream output
- [ ] The original failed job's status remains `error` (not overwritten); the retry is a new job
- [ ] Retry is available for any pipeline stage job (TTS, Veo, render, stitch, audit, resolve-batch)
- [ ] Jobs that are currently running or already completed cannot be retried (returns 409 Conflict)
- [ ] The retried job's SSE stream opens automatically in the UI
- [ ] If a prerequisite stage's output has been deleted since the original run, the retry fails with a clear error message

## Mapping to PRD

- Section 4.4 (Job Management — Job retry)
- Section 9.3 (Reliability — Job retry)
- Appendix A (Jobs API — `POST /api/jobs/:id/retry`)

## Technical Notes

- Job parameters are stored in the jobs database table at creation time
- Retry creates a new row in the jobs table with `retryOf: originalJobId` for traceability
- Rate limiting: max 3 retries per original job to prevent infinite retry loops
