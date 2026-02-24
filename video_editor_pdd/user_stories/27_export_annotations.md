# User Story 27: Export Annotations

**As a** director,
**I want to** export all annotations as a JSON file,
**So that** I can share review notes externally or back up my annotation data.

## Acceptance Criteria

- [ ] `GET /api/export` returns a downloadable JSON file containing all annotations with their analysis results
- [ ] The export includes all annotation fields: id, text, sectionId, timestamp, drawing paths, analysis, resolved status
- [ ] The export file is named `annotations_export_{date}.json`
- [ ] A [Download Export] button is accessible from the Review tab or a settings panel
- [ ] Export includes only the latest version of each annotation (not the full version history)
- [ ] Export works even if some annotations have not been analyzed yet (analysis fields are null)

## Mapping to PRD

- Appendix A (Metadata API — `GET /api/export`)

## Technical Notes

- Response headers: `Content-Type: application/json`, `Content-Disposition: attachment; filename="annotations_export_{date}.json"`
- The export format should be compatible with `POST /api/annotations` for potential future import functionality
- Large exports (100+ annotations with base64 images) may need streaming JSON serialization
