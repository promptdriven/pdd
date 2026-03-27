[split:]

# Section 3.7: Split Screen — Traditional Bug Fix vs. PDD

**Tool:** Split
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 2:17 - 2:25

## Visual Description

A split-screen comparison showing the fundamental difference between traditional bug fixing and the PDD approach.

**LEFT PANEL — "Traditional":** A vertical flowchart in muted red tones. Steps appear one by one:
1. Bug found →
2. Patch code →
3. Similar bug elsewhere →
4. Patch again →
5. Different bug →
6. Patch again...
An ellipsis trails off, suggesting infinite repetition. Each "patch" step gets a small band-aid icon.

**RIGHT PANEL — "PDD":** A vertical flowchart in bright green/blue tones. Steps appear one by one:
1. Bug found →
2. Add test (`pdd bug`) →
3. Regenerate (`pdd fix`) →
4. Bug impossible forever ✓
The final step glows — it's terminal. The chain is finite.

The left panel's steps keep extending downward (infinite), while the right panel's chain is complete and short (4 steps). The visual contrast is immediate: repetitive patching vs. permanent resolution.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Layout: Two 920px-wide panels with 80px center divider zone
- Divider: White (`#FFFFFF`), 2px solid line, 30% opacity
- Background: `#0A0F1A` (deep navy-black)

### Panel Configuration

#### Left Panel — "Traditional"
- Header: "TRADITIONAL" — Inter, 20px, bold (700), `#F87171` (muted red), centered at y: 120
- Flowchart: vertical, centered, starting at y: 200
- Step boxes: 260px × 40px, rounded 6px, `#1E1E2E` fill, `#F87171` at 0.2 border
- Step text: Inter, 14px, regular (400), `#CDD6F4`
- Arrows between steps: `#F87171` at 0.3, 1.5px, downward
- Band-aid icon: 16×16, `#F87171` at 0.4, to the right of each "Patch" step
- Trailing ellipsis: three dots animating (opacity pulse), `#F87171` at 0.3

#### Right Panel — "PDD"
- Header: "PDD" — Inter, 20px, bold (700), `#4ADE80` (green), centered at y: 120
- Flowchart: vertical, centered, starting at y: 200
- Step boxes: 280px × 40px, rounded 6px, `#1E1E2E` fill, `#4A90D9` at 0.2 border
- Step text: Inter, 14px, regular (400), `#CDD6F4`
- Code inline: JetBrains Mono, 13px, `#A6E3A1`
- Arrows: `#4A90D9` at 0.3, 1.5px, downward
- Final step: `#4ADE80` border at 0.5, glow `#4ADE80` at 0.15, 8px blur
- Checkmark: `✓` in `#4ADE80`, 18px, inside final step

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Split screen fades in. Headers appear: "TRADITIONAL" (left) and "PDD" (right).
2. **Frame 20-50 (0.67-1.67s):** Both sides: Step 1 "Bug found" appears simultaneously.
3. **Frame 50-80 (1.67-2.67s):** LEFT: "Patch code" + band-aid. RIGHT: "Add test (pdd bug)".
4. **Frame 80-110 (2.67-3.67s):** LEFT: "Similar bug elsewhere". RIGHT: "Regenerate (pdd fix)".
5. **Frame 110-140 (3.67-4.67s):** LEFT: "Patch again" + band-aid. RIGHT: "Bug impossible forever ✓" — final step glows.
6. **Frame 140-170 (4.67-5.67s):** LEFT: "Different bug" → "Patch again..." — the chain continues. RIGHT: Complete. Glow holds.
7. **Frame 170-200 (5.67-6.67s):** LEFT: Trailing ellipsis pulses — the cycle never ends. RIGHT: Static, resolved.
8. **Frame 200-240 (6.67-8s):** Hold. The contrast is stark: infinite left, terminal right.

### Typography
- Headers: Inter, 20px, bold (700)
- Steps: Inter, 14px, regular (400), `#CDD6F4`
- Code inline: JetBrains Mono, 13px, `#A6E3A1`

### Easing
- Step box fade-in: `easeOut(quad)` over 15 frames each
- Arrow draw: `easeOut(quad)` over 10 frames
- Final glow: `easeInOut(sine)` pulse on 30-frame cycle
- Ellipsis pulse: `easeInOut(sine)` on 20-frame cycle

## Narration Sync
> "In traditional development, a bug fix helps one place. In PDD, a test prevents that bug everywhere, forever."

Segment: `part3_mold_parts_011`

- **137.34s** (seg 011): Split screen appears — "In traditional development"
- **141.0s**: Steps building on both sides
- **143.0s**: "In PDD, a test prevents that bug everywhere, forever"
- **145.20s** (seg 011 ends): Hold on completed comparison

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <SplitScreen dividerColor="#FFFFFF" dividerWidth={2} dividerOpacity={0.3}>
      {/* Left: Traditional */}
      <PanelLeft>
        <Sequence from={0}>
          <FadeIn duration={15}>
            <Text text="TRADITIONAL" color="#F87171"
              font="Inter" size={20} weight={700} />
          </FadeIn>
        </Sequence>
        {TRADITIONAL_STEPS.map((step, i) => (
          <Sequence key={i} from={20 + i * 30}>
            <FadeIn duration={15}>
              <FlowStep text={step.text}
                borderColor="#F87171"
                icon={step.hasBandaid ? "bandaid" : undefined} />
            </FadeIn>
            <Sequence from={5}>
              <DrawArrow color="#F87171" opacity={0.3} />
            </Sequence>
          </Sequence>
        ))}
        <Sequence from={170}>
          <PulsingEllipsis color="#F87171" cycleFrames={20} />
        </Sequence>
      </PanelLeft>

      {/* Right: PDD */}
      <PanelRight>
        <Sequence from={0}>
          <FadeIn duration={15}>
            <Text text="PDD" color="#4ADE80"
              font="Inter" size={20} weight={700} />
          </FadeIn>
        </Sequence>
        {PDD_STEPS.map((step, i) => (
          <Sequence key={i} from={20 + i * 30}>
            <FadeIn duration={15}>
              <FlowStep text={step.text}
                borderColor="#4A90D9"
                glow={step.isFinal}
                checkmark={step.isFinal} />
            </FadeIn>
          </Sequence>
        ))}
      </PanelRight>
    </SplitScreen>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "split_screen",
  "layout": "vertical_50_50",
  "divider": { "color": "#FFFFFF", "width": 2, "opacity": 0.3 },
  "panels": {
    "left": {
      "header": "TRADITIONAL",
      "headerColor": "#F87171",
      "steps": ["Bug found", "Patch code", "Similar bug elsewhere", "Patch again", "Different bug", "Patch again..."],
      "infinite": true
    },
    "right": {
      "header": "PDD",
      "headerColor": "#4ADE80",
      "steps": ["Bug found", "Add test (pdd bug)", "Regenerate (pdd fix)", "Bug impossible forever ✓"],
      "infinite": false
    }
  },
  "narrationSegments": ["part3_mold_parts_011"],
  "durationSeconds": 8.0
}
```

---
