# User Story 23: Section Timestamp Mapping

**As a** director reviewing the full stitched video,
**I want** pausing at any timestamp to automatically identify the correct section and local timestamp,
**So that** annotations are scoped to the right section and Claude analyzes the correct source files.

## Acceptance Criteria

- [ ] After rendering (Stage 9), `durationSeconds` is populated for each section by running `ffprobe` on the rendered video
- [ ] `offsetSeconds` is computed as the cumulative sum of preceding section durations (based on section order in `project.json`)
- [ ] When the user pauses the full video at timestamp T, the app identifies which section contains T using `offsetSeconds` ranges
- [ ] The local timestamp within the section is computed as `T - section.offsetSeconds`
- [ ] Annotations created during full-video review automatically include the correct `sectionId` and local timestamp
- [ ] The video player displays both the full-video timestamp and the section-relative timestamp (e.g., "1:04.6 / Part 2 @ 0:23.4")
- [ ] If section durations change after re-rendering, `offsetSeconds` values are recalculated automatically

## Mapping to PRD

- Section 4.5 (Section Mapping — `durationSeconds` and `offsetSeconds`)
- Section 4.5.1 (Project Config Schema)

## Technical Notes

- `ffprobe` command: `ffprobe -v error -show_entries format=duration -of csv=p=0 {section}.mp4`
- Duration/offset values stored in `project.json` under each section entry
- Binary search on `offsetSeconds` array for efficient timestamp-to-section lookup
- Edge case: timestamp exactly at a section boundary should map to the later section
