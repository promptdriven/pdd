[Remotion]

# Section 6.2: First Module Checklist — What Makes a Good First Target

**Tool:** Remotion
**Duration:** ~12s (360 frames @ 30fps)
**Timestamp:** 22:24 - 22:36

## Visual Description
An animated checklist materializes to answer the viewer's immediate question: "What module should I try this on first?" Four criteria appear as checkbox items, each revealing with a checkmark animation and a brief one-line rationale. The list is intentionally practical and non-intimidating — the viewer should feel they can identify a candidate in their own codebase within seconds. As each criterion appears, a small illustrative icon animates beside it. The final state is a clean, scannable list the viewer could screenshot.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Section Label:** "Your First PDD Module" — `#4A90D9` at 0.6 opacity, 16px, uppercase tracking 2px, positioned at (160, 80)
- **Heading:** "Pick something that is..." — `#FFFFFF` at 0.9 opacity, 36px, positioned at (160, 130)
- **Checklist Items (each row 120px tall, starting Y=220, 130px vertical spacing):**
  - **Row 1 — "Self-contained"**
    - Checkbox: 28px square, border `rgba(255,255,255,0.2)` 2px → fills `#4A90D9` on check
    - Checkmark: `#FFFFFF`, animated stroke draw
    - Label: "Self-contained" — Inter 26px semi-bold, `#FFFFFF`
    - Rationale: "Few imports, no tangled dependencies" — Inter 16px, `#94A3B8`
    - Icon: Single box icon (no arrows in/out), `#4A90D9` at 0.3, at X=1500
  - **Row 2 — "Already has tests"**
    - Same checkbox pattern, fills `#5AAA6E` on check
    - Label: "Already has tests" — Inter 26px semi-bold, `#FFFFFF`
    - Rationale: "Even a handful — they become your first walls" — Inter 16px, `#94A3B8`
    - Icon: Small shield with checkmark, `#5AAA6E` at 0.3, at X=1500
  - **Row 3 — "Under 500 lines"**
    - Same checkbox pattern, fills `#D9944A` on check
    - Label: "Under 500 lines" — Inter 26px semi-bold, `#FFFFFF`
    - Rationale: "Fits comfortably in a single context window" — Inter 16px, `#94A3B8`
    - Icon: Document with "< 500" text, `#D9944A` at 0.3, at X=1500
  - **Row 4 — "Low-risk to replace"**
    - Same checkbox pattern, fills `#2AA198` on check
    - Label: "Low-risk to replace" — Inter 26px semi-bold, `#FFFFFF`
    - Rationale: "A utility, parser, formatter — not your auth system" — Inter 16px, `#94A3B8`
    - Icon: Small recycle/refresh arrows, `#2AA198` at 0.3, at X=1500

### Animation Sequence
1. **Frame 0-30 (0-1.0s):** Section label fades in. Heading text fades in with slight left-to-right wipe
2. **Frame 30-90 (1.0-3.0s):** Row 1 animates — checkbox border draws, checkmark strokes in, label and rationale fade in with 8px rightward drift. Icon fades in at right
3. **Frame 90-150 (3.0-5.0s):** Row 2 animates with same pattern, 60-frame stagger
4. **Frame 150-210 (5.0-7.0s):** Row 3 animates
5. **Frame 210-270 (7.0-9.0s):** Row 4 animates
6. **Frame 270-320 (9.0-10.67s):** All four checkboxes pulse briefly in unison (subtle scale 1.0→1.04→1.0) — a "checklist complete" feeling
7. **Frame 320-360 (10.67-12.0s):** Hold at final state. Faint ambient glow on all checkmarks

### Typography
- Section Label: Inter, 16px, bold (700), `#4A90D9` at 0.6, uppercase, letter-spacing 2px
- Heading: Inter, 36px, semi-bold (600), `#FFFFFF` at 0.9
- Item Label: Inter, 26px, semi-bold (600), `#FFFFFF`
- Item Rationale: Inter, 16px, regular (400), `#94A3B8`

### Easing
- Section label/heading fade: `easeOut(quad)`
- Checkbox border draw: `easeOut(cubic)`
- Checkmark stroke: `easeOut(cubic)`
- Label/rationale drift: `easeOut(quad)`
- Icon fade: `easeOut(quad)`
- Unison pulse: `easeInOut(sine)`

## Narration Sync
> "Start with one module. Pick something self-contained — few imports, no tangled dependencies. Something that already has a few tests. Something under five hundred lines. Something low-risk to replace — a utility, a parser, a formatter. Not your authentication system."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={360}>
  {/* Header */}
  <Sequence from={0} durationInFrames={30}>
    <SectionLabel text="Your First PDD Module" color="#4A90D9" y={80} />
    <HeadingText text="Pick something that is..." y={130} />
  </Sequence>

  {/* Checklist Rows */}
  {checklistItems.map((item, i) => (
    <Sequence key={item.id} from={30 + i * 60} durationInFrames={60}>
      <ChecklistRow
        label={item.label}
        rationale={item.rationale}
        checkColor={item.color}
        icon={item.icon}
        y={220 + i * 130}
      />
    </Sequence>
  ))}

  {/* Completion Pulse */}
  <Sequence from={270} durationInFrames={50}>
    <PulseAll targets="checkboxes" scale={1.04} />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "sectionLabel": "Your First PDD Module",
  "heading": "Pick something that is...",
  "items": [
    {
      "label": "Self-contained",
      "rationale": "Few imports, no tangled dependencies",
      "color": "#4A90D9",
      "icon": "box-isolated"
    },
    {
      "label": "Already has tests",
      "rationale": "Even a handful — they become your first walls",
      "color": "#5AAA6E",
      "icon": "shield-check"
    },
    {
      "label": "Under 500 lines",
      "rationale": "Fits comfortably in a single context window",
      "color": "#D9944A",
      "icon": "doc-small"
    },
    {
      "label": "Low-risk to replace",
      "rationale": "A utility, parser, formatter — not your auth system",
      "color": "#2AA198",
      "icon": "refresh-arrows"
    }
  ]
}
```

---
