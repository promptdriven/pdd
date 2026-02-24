# User Story 15: Prerequisite Auto-Run

**As a** video director,
**I want** triggering any pipeline stage to automatically run all incomplete upstream stages first,
**So that** I don't have to manually track and run dependencies — I just click the stage I want.

## Acceptance Criteria

- [ ] The pipeline has two parallel tracks: Audio (TTS script -> TTS render -> Audio sync) and Visual (Specs -> Veo)
- [ ] Both tracks converge at Composition Generation, then flow to Render -> Stitch -> Audit
- [ ] Clicking a downstream stage (e.g., Render) checks all upstream stages in the dependency graph
- [ ] Incomplete upstream stages are run automatically; independent branches run concurrently
- [ ] Sidebar badges update in real-time as each prerequisite completes
- [ ] If any prerequisite fails, the chain stops and the error is reported
- [ ] Navigation to any stage panel is always free regardless of upstream status (viewing != running)

## Mapping to PRD

- Section 4.6.1 (Prerequisite auto-run)

## Technical Notes

- Dependency graph is not a flat list — audio and visual tracks are independent until Stage 8
- Example: clicking [Render All] with Stages 3-8 incomplete runs audio track in parallel with visual track, then composition generation, then render
- SSE streams progress for each prerequisite stage
