[Remotion]

# Section 1.5: Code Churn & Refactoring Annotations — GitClear Data

**Tool:** Remotion
**Duration:** ~28s (840 frames @ 30fps)
**Timestamp:** 2:21 - 2:49

## Visual Description

New annotations materialize on the existing code cost chart, replacing or layering atop the GitHub/Uplevel annotations. These point to the shaded debt area, making the technical debt story concrete with GitClear's data.

**Annotation 1** (pointing to the shaded debt area):
- "Code churn: +44% (GitClear, 2025)"
- Fine print: "211M lines analyzed"

**Annotation 2** (pointing to the widening gap between solid and dashed lines):
- "Refactoring: −60%"
- Fine print: "Code revised within 2 weeks"

The debt area pulses subtly when these annotations appear, drawing attention to the growing gap. The picture visually "gets worse" — the annotations stack up to paint an increasingly alarming story.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (inherited)
- Previous annotations fade to 30% opacity as new ones appear

### Chart/Visual Elements

#### Annotation 1 — Code Churn
- Position: Right side, pointing into the shaded debt area
- Callout box: `#1E293B` fill, `#EF4444` 1.5px border, 8px corner radius
- Main text: "Code churn: +44%" — Inter 18px, bold (700), `#EF4444`
- Source: "(GitClear, 2025, 211M lines analyzed)" — Inter 12px, regular (400), `#94A3B8`
- Connector line: 1px `#EF4444` at 0.5, from callout into debt area

#### Annotation 2 — Refactoring Collapse
- Position: Below annotation 1, pointing to the gap
- Callout box: `#1E293B` fill, `#F59E0B` 1.5px border, 8px corner radius
- Main text: "Refactoring: −60%" — Inter 18px, bold (700), `#F59E0B`
- Connector line: 1px `#F59E0B` at 0.5, from callout to gap edge

#### Debt Area Pulse
- The shaded area between solid and dashed amber lines pulses: opacity oscillates 0.12 → 0.20 → 0.12
- Pulse syncs with annotation appearance

### Animation Sequence
1. **Frame 0-60 (0-2s):** Previous annotations (GitHub/Uplevel) fade to 30% opacity.
2. **Frame 60-150 (2-5s):** Debt area pulses. Annotation 1 materializes: connector draws, callout scales in, text types.
3. **Frame 150-360 (5-12s):** Hold. Narration covers GitClear data.
4. **Frame 360-450 (12-15s):** Annotation 2 materializes with connector pointing to the gap.
5. **Frame 450-840 (15-28s):** Both visible. Debt area continues gentle pulsing. The visual story is alarming.

### Typography
- Annotation main: Inter, 18px, bold (700), respective accent colors
- Source: Inter, 12px, regular (400), `#94A3B8`

### Easing
- Previous fade-out: `easeIn(quad)` over 30 frames
- Connector draw: `easeOut(quad)` over 30 frames
- Callout scale-in: `easeOut(back)` over 20 frames
- Debt pulse: `easeInOut(sine)` on 45-frame cycle

## Narration Sync
> "And GitClear confirmed it across 211 million lines of code. Since AI coding assistants arrived, code churn is up 44%... Meanwhile, refactoring collapsed by 60%. Developers aren't cleaning up. They're piling on."
> "But there's a second kind of debt hiding in there. One that's specific to AI-assisted development."

Segments: `part1_economics_012`, `part1_economics_013`

- **140.78s** (seg 012): Previous annotations fade, new ones begin — "And GitClear confirmed it"
- **145.0s**: Code churn annotation materializes
- **155.0s**: Refactoring annotation materializes
- **163.06s** (seg 012 ends / seg 013 starts): "But there's a second kind of debt"
- **168.62s** (seg 013 ends): Transition to debt layers zoom

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={840}>
  {/* Fade previous annotations */}
  <Sequence from={0}>
    <FadeOpacity from={1.0} to={0.3} duration={30}>
      <PreviousAnnotations />
    </FadeOpacity>
  </Sequence>

  {/* Debt area pulse */}
  <Sequence from={60}>
    <PulseOpacity
      target="debt_shaded_area"
      min={0.12} max={0.20}
      cycleFrames={45}
    />
  </Sequence>

  {/* Annotation 1: Code churn */}
  <Sequence from={60}>
    <AnnotationCallout
      targetArea="debt_area" targetX={2024}
      borderColor="#EF4444"
      mainText="Code churn: +44%"
      source="(GitClear, 2025, 211M lines analyzed)"
      position={{ x: 1380, y: 380 }}
    />
  </Sequence>

  {/* Annotation 2: Refactoring collapse */}
  <Sequence from={360}>
    <AnnotationCallout
      targetArea="debt_gap" targetX={2024}
      borderColor="#F59E0B"
      mainText="Refactoring: −60%"
      position={{ x: 1380, y: 480 }}
    />
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "annotation_overlay",
  "chartRef": "code_cost_generate_vs_patch",
  "annotations": [
    {
      "id": "gitclear_churn",
      "mainText": "Code churn: +44%",
      "source": "GitClear, 2025",
      "finePrint": "211M lines analyzed",
      "targetArea": "debt_area",
      "accentColor": "#EF4444"
    },
    {
      "id": "gitclear_refactoring",
      "mainText": "Refactoring: −60%",
      "source": "GitClear, 2025",
      "finePrint": "Code revised within 2 weeks",
      "targetArea": "debt_gap",
      "accentColor": "#F59E0B"
    }
  ],
  "narrationSegments": ["part1_economics_012", "part1_economics_013"]
}
```

---
