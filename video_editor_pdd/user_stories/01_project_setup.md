# User Story 01: Project Setup

**As a** video director,
**I want to** create a new video project by defining sections, TTS voice settings, and output resolution,
**So that** the entire pipeline knows the project structure without any hardcoded config.

## Acceptance Criteria

- [ ] User can enter a project name, select output resolution (e.g., 1920x1080), and configure TTS voice/speaker/rate
- [ ] User can add, edit, reorder, and remove sections in a section registry table
- [ ] Each section row has: Section ID, Video File, Remotion Composition ID, and Spec Directory
- [ ] Saving writes a valid `project.json` to disk and the server picks it up without restart
- [ ] Unsaved changes show a visual indicator and trigger a browser `beforeunload` warning
- [ ] Reopening the app loads existing `project.json` into the form

## Mapping to PRD

- Section 4.5.1 (Project Config Schema)
- Section 4.6.2 (Stage 1: Project Setup)
- Section 9.1 (Production Pipeline — Project setup)
- Section 9.3 (Reliability — Project config)

## Technical Notes

- `project.json` is the single source of truth; replaces the hardcoded `sections` array from the prototype's `server.js`
- Section rows should be inline-editable and drag-reorderable
- `PUT /api/project` endpoint persists config
