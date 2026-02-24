# User Story 10: Multi-Agent Audit

**As a** video director,
**I want to** run automated audits that compare rendered output against visual specs,
**So that** I can catch discrepancies (wrong colors, missing elements, timing issues) before manual review.

## Acceptance Criteria

- [ ] An audit table shows: Section, Pass count, Fail count, Status, and action buttons
- [ ] [Audit All Sections] launches parallel Claude Code agents (one per section)
- [ ] [Audit Section] dropdown scopes to a single section
- [ ] [View Report] expands the row to show per-spec pass/fail verdicts with one-line summaries
- [ ] FAIL rows show: [View Frame], [View Spec], and [Create Annotation] buttons
- [ ] [Create Annotation] pre-fills a new annotation in the Review tab with the audit finding and frame screenshot
- [ ] SSE streaming shows per-agent progress: "Agent 3/7: auditing part3_mold (spec 4/8)"

## Mapping to PRD

- Section 4.6.11 (Stage 10: Audit)
- Section 5.6 (Multi-Agent Audit Pipeline)

## Technical Notes

- `POST /api/pipeline/audit/run` with `{ sections?: [] }`
- Each agent: renders a still frame at segment midpoint via `npx remotion still`, compares against spec
- Output: `audits/AUDIT_SWEEP_{date}.md`, `specs/{section}/AUDIT_*.md`
- Audit bridges into the review/fix loop via [Create Annotation]
