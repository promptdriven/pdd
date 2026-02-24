# User Story 14: Job Management and Progress Streaming

**As a** video director,
**I want to** see real-time progress for any running pipeline job and retry failed jobs,
**So that** I always know what the system is doing and can recover from failures without re-running everything.

## Acceptance Criteria

- [ ] Every pipeline action returns a `jobId` and opens an SSE stream for real-time progress
- [ ] Progress events show: percentage, current step, and human-readable message
- [ ] On completion: green banner with result summary
- [ ] On error: red banner with error message
- [ ] If SSE fails, automatic fallback to polling `GET /api/jobs/:id` every 2 seconds
- [ ] Any failed job can be retried via `POST /api/jobs/:id/retry` without re-running upstream stages
- [ ] On server restart, all pending/running jobs are marked as error with "Server restarted during pipeline"
- [ ] Pipeline status sidebar badges refresh every 5 seconds via `GET /api/pipeline/status`

## Mapping to PRD

- Section 4.4 (Job Management)
- Section 4.6.1 (SSE streaming pattern)
- Section 9.3 (Reliability — Job retry)
- Appendix A (Jobs API, Common Response Schemas)

## Technical Notes

- SSE events: `progress`, `done`, `error`
- Job status: `pending` -> `running` -> `done` | `error`
- Stage badges: `not_started` (○), `running` (◌), `done` (●), `error` (✕)
- Only one batch job runs per section at a time
