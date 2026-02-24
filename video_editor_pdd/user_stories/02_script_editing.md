# User Story 02: Script Editing

**As a** video director,
**I want to** view and edit my source script (`main_script.md`) in a split-pane editor with a structured preview,
**So that** I can refine narration and visual descriptions before generating downstream artifacts.

## Acceptance Criteria

- [ ] Left pane displays a CodeMirror editor with Markdown syntax highlighting loaded with `narrative/main_script.md`
- [ ] Right pane shows a structured preview: `NARRATOR:` lines get a blue badge, `[VISUAL:]` blocks get a teal badge, `##` headers show section labels
- [ ] Edits auto-save to disk on a 1-second debounce via `PUT /api/project/script`
- [ ] The structured preview re-renders on every keystroke (debounced 200ms)
- [ ] The split divider is resizable by dragging
- [ ] [Generate TTS Script] button is enabled only when at least one `NARRATOR:` block exists

## Mapping to PRD

- Section 4.6.3 (Stage 2: Script Editor)

## Technical Notes

- CodeMirror 6 with Markdown language support (already in `package.json`)
- The structured preview is a parsed rendering, not a raw markdown render
