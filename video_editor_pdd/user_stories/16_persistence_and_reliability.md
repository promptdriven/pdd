# User Story 16: Database-Backed Persistence

**As a** video director,
**I want** annotations and job state stored in a real database (not a flat JSON file),
**So that** data is safe from corruption, supports concurrent access, and preserves history.

## Acceptance Criteria

- [ ] Annotations are stored in SQLite (already in `package.json` as `better-sqlite3`)
- [ ] Annotation history is preserved (edits create new versions, not overwrites)
- [ ] Jobs table tracks all pipeline jobs with status, timestamps, and parameters
- [ ] Concurrent API requests don't corrupt data
- [ ] Data survives server restarts without loss
- [ ] `GET /api/export` still works for downloading annotations

## Mapping to PRD

- Section 9.3 (Reliability — Database-backed persistence)
- Section 7 (Current State Assessment — Persistence is flat JSON file)

## Technical Notes

- Replace `data/annotations.json` with SQLite tables
- `better-sqlite3` is already a project dependency
- Schema should support: annotations, annotation_versions, jobs, pipeline_status
