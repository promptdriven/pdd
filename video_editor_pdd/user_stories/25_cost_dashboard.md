# User Story 25: Cost Dashboard

**As a** director,
**I want to** see Claude API, Veo, and Imagen costs per pipeline stage,
**So that** I can track spending and optimize my review/fix workflow.

## Acceptance Criteria

- [ ] A cost summary panel is accessible from the app (e.g., via a settings/info icon)
- [ ] Costs are tracked per pipeline stage: TTS script generation, spec generation, composition generation, Veo generation, audit, and resolve-batch
- [ ] Each job records its cost breakdown: Claude API tokens (input + output), Veo clip count, Imagen image count
- [ ] The dashboard shows per-session totals and cumulative project totals
- [ ] Cost estimates use configurable per-unit rates (e.g., $/1K tokens, $/clip, $/image) stored in `project.json`
- [ ] Local operations (TTS rendering, Remotion rendering, ffmpeg) show $0 cost
- [ ] Lambda rendering costs are tracked separately when Lambda opt-in is enabled

## Mapping to PRD

- Section 9.4 (Efficiency — Cost dashboard)
- Section 7 (What's Missing — Cost tracking)

## Technical Notes

- Claude token usage is available from the CLI's `--output-format json` response
- Veo and Imagen costs are estimated from API call counts (actual billing comes from Google Cloud)
- Store cost records in a `job_costs` SQLite table linked to `jobId`
- Default rate estimates: Claude ~$15/MTok input, ~$75/MTok output; Veo ~$0.50/clip; Imagen ~$0.02/image
