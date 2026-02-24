# User Story 11: Video Annotation (Spacebar Workflow)

**As a** video director reviewing a rendered video,
**I want to** pause the video, draw on the frame, and describe the issue via speech or text,
**So that** I can precisely communicate visual problems to the AI for automated fixing.

## Acceptance Criteria

- [ ] Pressing Space pauses the video, activates a drawing canvas overlay, and starts speech recognition
- [ ] Drawing tools available: freehand, rectangle, circle, arrow, text (keyboard shortcuts: F/R/C/A/T)
- [ ] User can speak a description (Web Speech API) and/or type text
- [ ] Pressing Space again: stops recording, captures the frame thumbnail, creates a composite image (video + drawings), saves the annotation, and resumes playback
- [ ] Additional shortcuts: D (draw mode), M (mic toggle), Ctrl+Z (undo drawing), K (play/pause), arrow keys (seek)
- [ ] Saved annotation includes: text content, input method, video timestamp, section ID, frame thumbnail, drawing paths, and composite image
- [ ] Annotations appear in a sidebar list grouped by section

## Mapping to PRD

- Section 4.2 (The Spacebar Workflow)
- Section 4.1 (Annotation Model)
- Section 9.2 (Review/Fix Loop — Video player with annotation)

## Technical Notes

- Drawing canvas: 1920x1080 internal resolution
- Annotation ID format: `ann_{timestamp}_{random}`
- Video timestamp maps to section via `offsetSeconds` from `project.json`
- `POST /api/annotations` to save; `POST /api/thumbnails` for frame captures
