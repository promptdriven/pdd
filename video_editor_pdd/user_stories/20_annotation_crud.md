# User Story 20: Annotation Edit and Delete

**As a** director,
**I want to** edit or delete annotations I've already created,
**So that** I can correct mistakes or remove irrelevant feedback before triggering fixes.

## Acceptance Criteria

- [ ] Each annotation in the sidebar has an [Edit] button that opens the annotation text for editing
- [ ] Edited annotations are saved via `PUT /api/annotations/:id` and the UI updates immediately
- [ ] Editing an annotation that has already been analyzed resets its analysis status to `pending` and re-triggers analysis
- [ ] Each annotation in the sidebar has a [Delete] button with a confirmation prompt
- [ ] Deleting an annotation calls `DELETE /api/annotations/:id` and removes it from the sidebar list
- [ ] Annotations that are part of a currently-running batch job cannot be edited or deleted (buttons disabled with tooltip)
- [ ] Annotation edit history is preserved in the database (edits create new versions, not overwrites)

## Mapping to PRD

- Appendix A (Annotations API — `PUT /api/annotations/:id`, `DELETE /api/annotations/:id`)
- Section 4.1 (Annotation Model)
- Section 9.3 (Reliability — annotation history)

## Technical Notes

- `PUT /api/annotations/:id` accepts partial updates (only the fields being changed)
- `DELETE /api/annotations/:id` returns 204 on success, 404 if not found, 409 if annotation is locked by a running job
- Version history: store previous annotation state in an `annotation_versions` table with foreign key to the annotation ID
