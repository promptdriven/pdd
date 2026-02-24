# User Story 28: Incremental Rendering

**As a** director fixing a single-frame issue,
**I want** the system to render only the frames around the fix instead of the entire section,
**So that** the fix-review cycle completes in seconds instead of minutes.

## Acceptance Criteria

- [ ] When a fix affects a known frame range, the renderer uses Remotion's `--frames` flag to render only the affected frames plus a buffer (e.g., 30 frames before and after)
- [ ] The incrementally rendered frames are composited into the existing section video via ffmpeg segment replacement
- [ ] The full section video is playable after incremental render without re-encoding the entire file
- [ ] Incremental render is used automatically when the fix's affected frame range can be determined (Remotion fixes with known BEATS constants)
- [ ] Full section render is used as fallback when the affected frame range cannot be determined
- [ ] The UI shows "Incremental render (frames 450-520)" or "Full render" to indicate which mode was used
- [ ] Incremental render time is at least 3x faster than full section render for localized fixes

## Mapping to PRD

- Section 9.4 (Efficiency — Incremental rendering)
- Section 10 (Known Limitations — full section re-render for any change)

## Technical Notes

- Remotion CLI: `npx remotion render --frames=450-520` to render a specific range
- ffmpeg segment replacement: extract the segment, replace with new frames, re-mux without re-encoding unchanged portions
- Frame range detection: parse the fix's modified BEATS constants to determine affected frame numbers
- Buffer size should be configurable (default: 1 second / 30 frames at 30fps)
- Edge case: if the fix changes global constants (colors, fonts), fall back to full render
