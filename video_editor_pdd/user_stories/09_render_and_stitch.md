# User Story 09: Render and Stitch

**As a** video director,
**I want to** render individual sections and stitch them into a full video,
**So that** I can see the assembled output and proceed to review.

## Acceptance Criteria

- [ ] A section render table shows: Section, Duration, Status, Progress bar, and action buttons
- [ ] [Play] opens the rendered section `.mp4` in a video modal
- [ ] [Re-render] triggers rendering for that section
- [ ] [Render] dropdown offers: Render All, Render Missing, Render Selected Section
- [ ] Up to 3 sections can render in parallel, each with its own progress bar
- [ ] Progress updates stream via SSE with per-section percentage
- [ ] [Stitch Full Video] runs `ffmpeg concat` to assemble all sections
- [ ] Full video panel shows: file size, duration (from ffprobe), and [Open in Review] button
- [ ] Prerequisite auto-run: triggering render auto-runs all incomplete upstream stages first

## Mapping to PRD

- Section 4.6.10 (Stage 9: Render + Stitch)
- Section 5.5 (Rendering)
- Section 9.1 (Production Pipeline — Section render + stitch, Progress streaming)

## Technical Notes

- `POST /api/pipeline/render/run` with `{ sections?: [] }`
- `POST /api/pipeline/stitch/run`
- Local rendering: `npx remotion render src/remotion/index.ts {compositionId} --output {section.mp4}`
- Stitch: `ffmpeg -f concat -safe 0 -i concat.txt -c copy full_video.mp4`
- Lambda rendering is opt-in via `project.json` render config
- Duration/offset populated by ffprobe after render, written back to `project.json`
