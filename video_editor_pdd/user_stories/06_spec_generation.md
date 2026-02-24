# User Story 06: Visual Spec Generation

**As a** video director,
**I want to** generate visual spec files from my source script using Claude Code and edit them inline,
**So that** every shot has a detailed spec (tool assignment, duration, color palette, animation params) before any code is written.

## Acceptance Criteria

- [ ] Specs are organized in collapsible section groups (collapse state persisted in localStorage)
- [ ] Each spec shows a visual type badge: `[Remotion]` (blue), `[veo:]` (purple), `[title:]` (gray), `[split:]` (orange)
- [ ] Each spec has [Edit] and [Regenerate] buttons
- [ ] [Edit] opens the spec in an inline CodeMirror Markdown editor (auto-saves on blur)
- [ ] [Regenerate] re-generates that single spec file via Claude Code
- [ ] [Generate All Specs] generates specs for all sections; [Regenerate Section] scopes to one section
- [ ] SSE progress is shown in an expandable drawer at the bottom

## Mapping to PRD

- Section 4.6.7 (Stage 6: Spec Generation)
- Section 5.1 (Spec-Driven Approach)
- Section 9.1 (Production Pipeline — Spec generation)

## Technical Notes

- `POST /api/pipeline/specs/run` with `{ sections?: [], files?: [] }`
- Specs include: tool assignment, duration, visual description, color palette (hex), typography, narration sync points, transitions
- Visual type prefixes in specs: `veo:filename`, `ComponentName`, `title:Text`, `title_over_code:Text`, `code_regen:label`
