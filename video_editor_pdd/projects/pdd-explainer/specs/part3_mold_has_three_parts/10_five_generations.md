[Remotion]

# Section 3.10: Five Generations — Pick the One That Passes

**Tool:** Remotion
**Duration:** ~18s (540 frames @ 30fps)
**Timestamp:** 2:06 - 2:24

## Visual Description

Five code panels appear side by side, like film frames or a contact sheet. Each panel shows a different code generation from the same prompt — different variable names, slightly different structures, but all attempting the same task. The panels are tall and narrow, arranged horizontally across the screen.

Two panels have red X marks overlaid — they failed tests. Two have yellow warning triangles — they have issues. One glows green with a checkmark — it passes all tests. The green panel pulses and gets highlighted. A label appears below: "Generate five. Pick the one that passes all tests."

The visual makes the point: you don't need perfection on every run. You need one success out of N attempts. The walls (tests) are the filter.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 40px spacing, `#1E293B` at 0.03

### Chart/Visual Elements

#### Code Panels (5)
- Each panel: 300×600px, arranged at x positions [96, 420, 744, 1068, 1392]
- Background: `#1E1E2E` (VS Code dark), rounded 6px, 1px border
- Code: JetBrains Mono, 9px, syntax-highlighted, 30-40 lines visible
- Each panel has slightly different code (different var names, structure)

#### Status Overlays
- Panel 1 (fail): Large red X, 80px, `#EF4444` at 0.7, centered. Border turns `#EF4444` at 0.3.
- Panel 2 (warn): Yellow warning triangle, 60px, `#F59E0B` at 0.6, centered. Border turns `#F59E0B` at 0.2.
- Panel 3 (fail): Large red X, 80px, `#EF4444` at 0.7, centered. Border turns `#EF4444` at 0.3.
- Panel 4 (warn): Yellow warning triangle, 60px, `#F59E0B` at 0.6, centered. Border turns `#F59E0B` at 0.2.
- Panel 5 (pass): Green checkmark, 80px, `#4ADE80` at 0.8, centered. Border turns `#4ADE80` at 0.4. Glow: 20px radius, `#4ADE80` at 0.1.

#### Label
- "Generate five. Pick the one that passes all tests." — Inter, 18px, bold, `#E2E8F0` at 0.7, centered at y: 900
- "The walls don't care how many attempts it took." — Inter, 14px, `#94A3B8` at 0.5, centered at y: 940

### Animation Sequence
1. **Frame 0-90 (0-3s):** Five panels slide in from bottom, staggered 10 frames apart. All appear as neutral code.
2. **Frame 90-150 (3-5s):** Panel 1 gets red X — test failure flash. Panel 3 gets red X.
3. **Frame 150-210 (5-7s):** Panel 2 gets yellow warning. Panel 4 gets yellow warning.
4. **Frame 210-300 (7-10s):** Panel 5 gets green checkmark. Glow effect blooms. Border brightens. Other panels dim to 0.3.
5. **Frame 300-420 (10-14s):** Green panel scales up slightly (1.05×). Label appears below.
6. **Frame 420-540 (14-18s):** Hold. Sub-label appears. The point is clear.

### Typography
- Code: JetBrains Mono, 9px, syntax-highlighted
- Status icons: 60-80px, respective status colors
- Main label: Inter, 18px, bold (700), `#E2E8F0` at 0.7
- Sub-label: Inter, 14px, `#94A3B8` at 0.5

### Easing
- Panel slide-in: `easeOut(cubic)` over 20 frames, 30px from bottom
- Status overlay: `easeOut(expo)` over 10 frames — sharp appearance
- Green glow bloom: `easeOut(cubic)` over 30 frames
- Panel dim: `easeOut(quad)` over 20 frames
- Green scale-up: `easeOut(back)` over 15 frames
- Label fade-in: `easeOut(quad)` over 20 frames

## Narration Sync
> "Now — you might be thinking: 'But LLMs don't follow instructions reliably.' You're right. Today. But PDD doesn't need perfection on every run. Generate five versions. Pick the one that passes all tests. The walls don't care how many attempts it took."

Segment: `part3_mold_has_three_parts_015`

- **2:06** ("LLMs don't follow instructions"): Five panels slide in
- **2:14** ("doesn't need perfection"): Red X and yellow warnings appear
- **2:19** ("Pick the one"): Green checkmark blooms on panel 5

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={540}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={40} color="#1E293B" opacity={0.03} />

    {/* Five code panels */}
    {PANELS.map((panel, i) => (
      <Sequence from={i * 10} key={panel.id}>
        <SlideUp distance={30} duration={20}>
          <CodePanel
            x={panel.x} y={180} width={300} height={600}
            code={panel.code} font="JetBrains Mono" fontSize={9}>

            {/* Status overlay */}
            <Sequence from={90 + panel.statusDelay}>
              <StatusOverlay
                type={panel.status}
                size={panel.status === 'pass' ? 80 : panel.status === 'fail' ? 80 : 60}
                color={panel.statusColor}
                glow={panel.status === 'pass'}
                glowRadius={20} />
            </Sequence>
          </CodePanel>
        </SlideUp>

        {/* Dim non-passing panels */}
        {panel.status !== 'pass' && (
          <Sequence from={210}>
            <FadeOpacity to={0.3} duration={20} />
          </Sequence>
        )}
      </Sequence>
    ))}

    {/* Labels */}
    <Sequence from={300}>
      <FadeIn duration={20}>
        <Text text="Generate five. Pick the one that passes all tests."
          font="Inter" size={18} weight={700}
          color="#E2E8F0" opacity={0.7}
          x={960} y={900} align="center" />
      </FadeIn>
    </Sequence>
    <Sequence from={420}>
      <FadeIn duration={20}>
        <Text text="The walls don't care how many attempts it took."
          font="Inter" size={14}
          color="#94A3B8" opacity={0.5}
          x={960} y={940} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_diagram",
  "diagramId": "five_generations",
  "panels": [
    { "id": "gen_1", "status": "fail", "color": "#EF4444", "statusDelay": 0 },
    { "id": "gen_2", "status": "warn", "color": "#F59E0B", "statusDelay": 60 },
    { "id": "gen_3", "status": "fail", "color": "#EF4444", "statusDelay": 0 },
    { "id": "gen_4", "status": "warn", "color": "#F59E0B", "statusDelay": 60 },
    { "id": "gen_5", "status": "pass", "color": "#4ADE80", "statusDelay": 120 }
  ],
  "label": "Generate five. Pick the one that passes all tests.",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_mold_has_three_parts_015"]
}
```

---
