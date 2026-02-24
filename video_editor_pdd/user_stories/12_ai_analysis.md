# User Story 12: AI Analysis of Annotations

**As a** video director,
**I want** each annotation to be automatically analyzed by Claude to determine severity, category, and fix type,
**So that** I know what kind of fix is needed (Remotion code / Veo clip / TTS audio) before applying it.

## Acceptance Criteria

- [ ] Analysis runs automatically when an annotation is saved
- [ ] Claude receives: spec files, main script section, Remotion source, TTS script section, Veo prompt (if applicable), frame screenshot, and markup composite
- [ ] Claude returns structured JSON: severity, category, summary, technical assessment, suggested fixes, relevant files, and `fixType` (`remotion` | `veo` | `tts`)
- [ ] Analysis status is shown on each annotation: pending -> analyzing -> completed / error
- [ ] Completed analysis shows a severity badge and fixType badge
- [ ] Analysis errors are displayed inline with an option to retry

## Mapping to PRD

- Section 4.3 (Claude Integration — Analysis)
- Section 4.1 (Annotation Model — analysis field)
- Section 9.2 (Review/Fix Loop — AI analysis)

## Technical Notes

- `POST /api/annotations/:id/analyze`
- Claude invoked in read-only mode: `--allowedTools Read,Glob`
- Analysis scoped to correct section via section registry mapping
- Should use Claude's structured output / tool_use mode instead of free-form JSON parsing (per §9.3)
