# User Story 07: Veo Video Clip Generation

**As a** video director,
**I want to** generate AI video clips from specs using character references and frame chaining,
**So that** I get visually consistent live-action footage for every veo-type segment.

## Acceptance Criteria

- [ ] A character references panel shows portrait thumbnails with a [Regenerate] button for each
- [ ] A frame chaining panel shows the dependency graph (portrait -> clip A -> clip B -> ...)
- [ ] A clip list table shows: #, Clip ID, Section, Aspect Ratio, Status
- [ ] Clips with stale upstream dependencies show a warning badge
- [ ] [Generate All] / [Generate Missing] / section-scoped dropdown trigger generation
- [ ] Split-screen clips (left + right 9:16 -> 16:9) show an auto-composite checkbox when both sides are done
- [ ] SSE streaming shows per-clip progress with estimated time remaining
- [ ] Generated clips can be previewed inline

## Mapping to PRD

- Section 4.6.8 (Stage 7: Veo Generation)
- Section 5.3 (Video Generation — Imagen + Veo)
- Section 8.3 (Character Consistency in Veo)

## Technical Notes

- `POST /api/pipeline/veo/run` with `{ clips?: [] }`
- Imagen 3.0 for reference portraits; Veo 3.1 for clip generation
- Frame chaining: last frame of clip N becomes reference for clip N+1
- Split-screen compositing via `ffmpeg hstack`
- Max concurrent Veo generations configurable in `project.json`
