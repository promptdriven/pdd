[split:]

# Section 3.8: Traditional vs PDD — Bug Fix Comparison

**Tool:** Split
**Duration:** ~18s (540 frames @ 30fps)
**Timestamp:** 1:34 - 1:52

## Visual Description

A vertical split screen comparing bug-fix workflows. Both sides show a timeline of events flowing downward.

**LEFT — "Traditional":** A cascade of patch-and-repeat. "Bug found" → "Patch code" → "Similar bug elsewhere" → "Patch again" → "Different bug" → "Patch again..." Each step is a red-tinted card. The chain grows longer, implying endless repetition. The steps get slightly less crisp, slightly more faded, as the cycle continues.

**RIGHT — "PDD":** A clean three-step flow. "Bug found" → "Add test (`pdd bug`)" → "Regenerate (`pdd fix`)" → "Bug impossible forever." Each step is a green-tinted card. After the final step, a lock icon appears with "∞" — the fix is permanent. The flow is short, clean, and final.

The contrast is stark: left side is an endless chain, right side terminates cleanly.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Split line: 2px vertical divider at x: 960, color `#334155` at 0.15

### Chart/Visual Elements

#### Left Panel — Traditional
- Header: "TRADITIONAL" — Inter, 20px, bold, `#EF4444` at 0.7, centered at y: 80
- Flow cards (top to bottom):
  1. "Bug found" — 300×50px, bg `#1E1015`, border `#EF4444` at 0.3, centered at y: 180
  2. "→ Patch code" — y: 270
  3. "Similar bug elsewhere" — y: 360
  4. "→ Patch again" — y: 450
  5. "Different bug" — y: 540
  6. "→ Patch again..." — y: 630, faded to 0.4
  7. "..." — y: 720, faded to 0.2 (cycle continues)
- Connecting arrows: 1px, `#EF4444` at 0.3, vertical between cards
- Each card: Inter, 14px, `#EF4444`, on dark red bg

#### Right Panel — PDD
- Header: "PDD" — Inter, 20px, bold, `#4ADE80` at 0.7, centered at y: 80
- Flow cards:
  1. "Bug found" — 300×50px, bg `#0F1E15`, border `#4ADE80` at 0.3, centered at y: 180
  2. "→ Add test (pdd bug)" — y: 320
  3. "→ Regenerate (pdd fix)" — y: 460
  4. "Bug impossible forever" — y: 600, with lock icon and glow
- Connecting arrows: 1px, `#4ADE80` at 0.4
- Final card has subtle glow: `#4ADE80` at 0.1, 20px radius
- Lock icon: 24px, `#4ADE80` at 0.6, right of final card text

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Split line fades in.
2. **Frame 15-60 (0.5-2s):** Both headers appear. "Bug found" cards appear on both sides simultaneously.
3. **Frame 60-180 (2-6s):** LEFT: Cards cascade downward — each appearing every 30 frames. The cycle builds. RIGHT: "Add test" card appears.
4. **Frame 180-300 (6-10s):** LEFT: Continues cascading — "Different bug", more patches. Fading as it goes. RIGHT: "Regenerate" card appears.
5. **Frame 300-420 (10-14s):** LEFT: "..." appears — the cycle is endless. RIGHT: "Bug impossible forever" appears with lock icon and glow.
6. **Frame 420-540 (14-18s):** Hold. The contrast is complete. LEFT side fades slightly. RIGHT side glows.

### Typography
- Headers: Inter, 20px, bold (700), respective panel color at 0.7
- Card text: Inter, 14px, semi-bold (600), respective panel color
- Lock icon: Material Icons, 24px, `#4ADE80`

### Easing
- Split line: `easeOut(quad)` over 15 frames
- Card appear: `easeOut(cubic)` over 15 frames, 10px upward slide
- Left fade progression: linear decay from 0.8 to 0.2
- Lock glow: `easeInOut(sine)` on 40-frame cycle
- Right panel glow: `easeOut(cubic)` over 30 frames

## Narration Sync
> "In traditional development, a bug fix helps one place. In PDD, a test prevents that bug everywhere, forever."

Segment: `part3_mold_has_three_parts_013`

- **1:34** ("traditional development"): Split screen appears, both timelines building
- **1:42** ("PDD, a test prevents"): Right side reaches "Bug impossible forever"
- **1:50** (hold): Contrast complete, transition approaching

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={540}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Left panel — Traditional */}
    <Panel x={0} width={958}>
      <FadeIn duration={15}>
        <Text text="TRADITIONAL" font="Inter" size={20}
          weight={700} color="#EF4444" opacity={0.7}
          x={479} y={80} align="center" />
      </FadeIn>
      {TRAD_STEPS.map((step, i) => (
        <Sequence from={15 + i * 30} key={step.id}>
          <FlowCard
            text={step.text} y={step.y}
            bg="#1E1015" border="#EF4444"
            textColor="#EF4444"
            opacity={step.opacity}
            slideUp={10} fadeDuration={15} />
          {i > 0 && <FlowArrow fromY={step.y - 50} toY={step.y} color="#EF4444" />}
        </Sequence>
      ))}
    </Panel>

    {/* Split divider */}
    <FadeIn duration={15}>
      <SplitLine x={960} color="#334155" opacity={0.15} width={2} />
    </FadeIn>

    {/* Right panel — PDD */}
    <Panel x={962} width={958}>
      <FadeIn duration={15}>
        <Text text="PDD" font="Inter" size={20}
          weight={700} color="#4ADE80" opacity={0.7}
          x={479} y={80} align="center" />
      </FadeIn>
      {PDD_STEPS.map((step, i) => (
        <Sequence from={15 + i * 90} key={step.id}>
          <FlowCard
            text={step.text} y={step.y}
            bg="#0F1E15" border="#4ADE80"
            textColor="#4ADE80"
            icon={step.icon} glow={step.glow}
            slideUp={10} fadeDuration={15} />
          {i > 0 && <FlowArrow fromY={step.y - 80} toY={step.y} color="#4ADE80" />}
        </Sequence>
      ))}
    </Panel>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "split_screen",
  "layout": "vertical_split",
  "splitPosition": 960,
  "leftPanel": {
    "header": "TRADITIONAL",
    "headerColor": "#EF4444",
    "steps": [
      { "text": "Bug found", "opacity": 0.8 },
      { "text": "→ Patch code", "opacity": 0.8 },
      { "text": "Similar bug elsewhere", "opacity": 0.7 },
      { "text": "→ Patch again", "opacity": 0.6 },
      { "text": "Different bug", "opacity": 0.5 },
      { "text": "→ Patch again...", "opacity": 0.4 },
      { "text": "...", "opacity": 0.2 }
    ],
    "thematicRole": "endless_cycle"
  },
  "rightPanel": {
    "header": "PDD",
    "headerColor": "#4ADE80",
    "steps": [
      { "text": "Bug found" },
      { "text": "→ Add test (pdd bug)" },
      { "text": "→ Regenerate (pdd fix)" },
      { "text": "Bug impossible forever", "icon": "lock", "glow": true }
    ],
    "thematicRole": "permanent_fix"
  },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_mold_has_three_parts_013"]
}
```

---
