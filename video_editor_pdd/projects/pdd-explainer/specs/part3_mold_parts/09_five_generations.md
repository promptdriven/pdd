[Remotion]

# Section 3.9: Five Generations — Pick the One That Passes

**Tool:** Remotion
**Duration:** ~18s (540 frames @ 30fps)
**Timestamp:** 2:44 - 3:02

## Visual Description

Five code generation outputs appear side by side, like film frames or contact sheet thumbnails. Each is a mini code editor panel showing a slightly different implementation of the same module.

- Generation 1: Red X mark overlay — fails tests. A few red-highlighted lines.
- Generation 2: Red X mark overlay — fails tests. Different failure.
- Generation 3: Yellow warning triangle — partial pass, some edge cases fail.
- Generation 4: Yellow warning triangle — partial pass, different issues.
- Generation 5: Glowing green checkmark — all tests pass. Green border glow.

Below the five panels, a label materializes: "Generate five. Pick the one that passes all tests."

The winning generation (5) scales up slightly and pulses with a green glow while the others dim. The message: perfection per generation is unnecessary. The walls (tests) select for correctness.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)

### Chart/Visual Elements

#### Code Panels (5 total)
- Each panel: 320px × 400px, `#1E1E2E` fill, `#334155` border 1px, rounded 8px
- Arranged horizontally with 24px gaps, centered at y: 420
- Total width: 5 × 320 + 4 × 24 = 1696px, centered from x: 112 to x: 1808
- Code inside: faux syntax-highlighted lines (6-8 visible lines per panel)
- Font: JetBrains Mono, 10px, various syntax colors

#### Status Overlays
- Red X: `#EF4444`, 48px, centered in panel, semi-transparent background `#EF4444` at 0.08
- Yellow warning: `#FBBF24`, 48px triangle icon, background `#FBBF24` at 0.06
- Green checkmark: `#4ADE80`, 48px, border glow `#4ADE80` at 0.3, 12px blur

#### Panel Header Badges
- Gen 1-5 labels: "Gen 1" through "Gen 5" — Inter, 11px, semi-bold (600), `#64748B`
- Positioned top-left of each panel

#### Label
- "Generate five. Pick the one that passes all tests." — Inter, 20px, semi-bold (600), `#E2E8F0`
- Centered at y: 700

### Animation Sequence
1. **Frame 0-30 (0-1s):** First panel slides up from below with fade-in. Faux code visible.
2. **Frame 30-60 (1-2s):** Panels 2-5 appear in rapid succession (8 frames apart).
3. **Frame 60-120 (2-4s):** Hold. All five panels visible, no status marks yet.
4. **Frame 120-150 (4-5s):** Red X stamps onto panels 1 and 2 with a brief shake animation.
5. **Frame 150-180 (5-6s):** Yellow warnings appear on panels 3 and 4 with a subtle wobble.
6. **Frame 180-240 (6-8s):** Green checkmark appears on panel 5 with a radial glow burst. Panel 5 border transitions to `#4ADE80`.
7. **Frame 240-330 (8-11s):** Panel 5 scales up slightly (1.0 → 1.08). Panels 1-4 dim (opacity to 0.4). Green glow pulses.
8. **Frame 330-420 (11-14s):** Label fades in below: "Generate five. Pick the one that passes all tests."
9. **Frame 420-540 (14-18s):** Hold. The winning generation is highlighted. The message is clear.

### Typography
- Panel headers: Inter, 11px, semi-bold (600), `#64748B`
- Code: JetBrains Mono, 10px, syntax colors
- Label: Inter, 20px, semi-bold (600), `#E2E8F0`

### Easing
- Panel slide-up: `easeOut(cubic)` over 20 frames
- X stamp: `easeOut(back)` over 10 frames with 3px shake
- Warning wobble: `easeOut(elastic)` over 12 frames
- Checkmark burst: `easeOut(expo)` over 15 frames
- Panel 5 scale: `easeOut(quad)` over 20 frames
- Dim others: `easeOut(quad)` over 20 frames
- Label fade-in: `easeOut(quad)` over 20 frames

## Narration Sync
> "Now — you might be thinking: 'But LLMs don't follow instructions reliably.' You're right. Today. But PDD doesn't need perfection on every run. Generate five versions. Pick the one that passes all tests. The walls don't care how many attempts it took."

Segment: `part3_mold_parts_013`

- **164.22s** (seg 013): Five panels begin appearing
- **168.0s**: All panels visible
- **172.0s**: Status marks appear — "PDD doesn't need perfection"
- **176.0s**: Green checkmark on panel 5 — "Pick the one that passes"
- **180.0s**: Label appears — "The walls don't care how many attempts"
- **181.90s** (seg 013 ends): Hold on highlighted winner

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={540}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* Five code generation panels */}
    {GENERATIONS.map((gen, i) => (
      <Sequence key={i} from={i * 8}>
        <SlideUp distance={30} duration={20}>
          <FadeIn duration={20}>
            <CodePanel
              x={112 + i * 344} y={220}
              width={320} height={400}
              code={gen.code}
              headerLabel={`Gen ${i + 1}`}
            />
          </FadeIn>
        </SlideUp>
      </Sequence>
    ))}

    {/* Status overlays */}
    {/* Red X on panels 1, 2 */}
    <Sequence from={120}>
      <StampOverlay panels={[0, 1]} icon="x"
        color="#EF4444" size={48}
        shakeAmount={3} duration={10} />
    </Sequence>

    {/* Yellow warning on panels 3, 4 */}
    <Sequence from={150}>
      <StampOverlay panels={[2, 3]} icon="warning"
        color="#FBBF24" size={48}
        wobble duration={12} />
    </Sequence>

    {/* Green checkmark on panel 5 */}
    <Sequence from={180}>
      <GlowBurst color="#4ADE80" radius={40} duration={15} />
      <StampOverlay panels={[4]} icon="check"
        color="#4ADE80" size={48} />
    </Sequence>

    {/* Highlight panel 5, dim others */}
    <Sequence from={240}>
      <ScaleTransition target={4} from={1.0} to={1.08} duration={20} />
      <DimPanels panels={[0, 1, 2, 3]} toOpacity={0.4} duration={20} />
    </Sequence>

    {/* Label */}
    <Sequence from={330}>
      <FadeIn duration={20}>
        <Text text="Generate five. Pick the one that passes all tests."
          font="Inter" size={20} weight={600} color="#E2E8F0"
          x={960} y={700} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "multi_generation",
  "generationCount": 5,
  "results": [
    { "gen": 1, "status": "fail", "icon": "x", "color": "#EF4444" },
    { "gen": 2, "status": "fail", "icon": "x", "color": "#EF4444" },
    { "gen": 3, "status": "partial", "icon": "warning", "color": "#FBBF24" },
    { "gen": 4, "status": "partial", "icon": "warning", "color": "#FBBF24" },
    { "gen": 5, "status": "pass", "icon": "check", "color": "#4ADE80" }
  ],
  "label": "Generate five. Pick the one that passes all tests.",
  "narrationSegments": ["part3_mold_parts_013"],
  "durationSeconds": 18.0
}
```

---
