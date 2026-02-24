# User Story 08: Remotion Composition Generation

**As a** video director,
**I want to** trigger Claude Code to write Remotion compositions from specs and verify all required assets are staged,
**So that** every visual segment has renderable React code backed by the correct audio and video assets.

## Acceptance Criteria

- [ ] A component list shows all Remotion components grouped by section, with status badges
- [ ] Each component has [Preview] (renders a still frame via `npx remotion still`) and [Regenerate] buttons
- [ ] Section wrappers are listed separately with the same controls
- [ ] [Generate All Compositions] batches all components and wrappers in a single job
- [ ] An asset staging manifest shows expected vs. present files in `remotion/public/`
- [ ] Missing assets show [Stage Now]; [Stage All Missing] stages everything at once
- [ ] Error tooltips show the last Claude Code error for failed components

## Mapping to PRD

- Section 4.6.9 (Stage 8: Composition Generation)
- Section 5.4 (Remotion Composition Architecture)
- Section 9.1 (Production Pipeline — Composition generation, Asset staging)

## Technical Notes

- `POST /api/pipeline/compositions/run` with `{ ids?: [] }`
- `POST /api/pipeline/asset-staging/run` with `{ files?: [] }`
- Compositions follow the pattern: `XX-CompositionName/{CompositionName.tsx, constants.ts, index.ts}`
- Section wrappers contain `VISUAL_SEQUENCE` arrays and `BEATS` constants from Whisper timestamps
- Asset filenames must match `staticFile()` references in composition code
