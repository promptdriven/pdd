[title:]

# Section 6.1: Where to Start — Section Title Card

**Tool:** Title
**Duration:** ~3s (90 frames @ 30fps)
**Timestamp:** 0:00 - 0:03

## Visual Description

A brief, confident section title card. "WHERE TO START" appears in clean, large typography against the deep navy-black background. Unlike earlier section titles which had taglines, this one is direct — no subtitle. The section number "PART 6" sits above, understated. A faint ghost outline of a codebase tree structure sits behind the text at very low opacity, previewing the legacy-code theme of this section.

The card is intentionally short — this section is practical, not conceptual, so the title gets out of the way quickly.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.04

### Chart/Visual Elements

#### Title Text
- "WHERE TO START" — Inter, 72px, bold (800), `#E2E8F0` at 0.95, centered at y: 500
- Tracking: 5px letter-spacing

#### Section Number
- "PART 6" — Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px, centered at y: 440

#### Background Ghost (codebase tree)
- Vertical trunk line: 2px, `#334155` at 0.04, from (960, 300) to (960, 780)
- Branch lines: 6 horizontal branches, alternating left/right, 80-140px wide, `#334155` at 0.03
- Small file icons at branch endpoints: 8x10px rectangles, `#334155` at 0.03
- Overall effect: a ghostly file-tree skeleton

### Animation Sequence
1. **Frame 0-10 (0-0.33s):** Background fades in. Blueprint grid appears. Ghost tree draws with stroke-dashoffset.
2. **Frame 10-25 (0.33-0.83s):** "PART 6" fades in. `easeOutQuad`.
3. **Frame 25-50 (0.83-1.67s):** "WHERE TO START" scales from 0.9 → 1.0 and fades in. `easeOutCubic`.
4. **Frame 50-75 (1.67-2.5s):** Hold. Ghost tree pulses once subtly.
5. **Frame 75-90 (2.5-3s):** Everything fades out. `easeInQuad`.

### Typography
- Section label: Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px
- Title: Inter, 72px, bold (800), `#E2E8F0` at 0.95, letter-spacing 5px

### Easing
- Title scale-in: `easeOut(cubic)` over 25 frames
- Section label fade: `easeOut(quad)` over 15 frames
- Ghost tree draw: `easeInOut(cubic)` over 20 frames
- Fade-out: `easeIn(quad)` over 15 frames

## Narration Sync
> "Now — you don't work on a greenfield project. Nobody does."

Segment: `where_to_start_001`

- **0:00** ("Now"): Title card appears
- **0:01** ("you don't work"): Title fully visible
- **0:03** (title fades): Transition to legacy codebase visual

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={90}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.04} />

    {/* Ghost codebase tree */}
    <Sequence from={0}>
      <StrokeDraw duration={20}>
        <CodebaseTree cx={960} cy={540} color="#334155"
          trunkOpacity={0.04} branchOpacity={0.03} />
      </StrokeDraw>
    </Sequence>

    {/* Section label */}
    <Sequence from={10}>
      <FadeIn duration={15}>
        <Text text="PART 6" font="Inter" size={14}
          weight={600} color="#64748B" opacity={0.5}
          letterSpacing={4} x={960} y={440} align="center" />
      </FadeIn>
    </Sequence>

    {/* Title */}
    <Sequence from={25}>
      <ScaleIn from={0.9} to={1.0} duration={25}>
        <FadeIn duration={25}>
          <Text text="WHERE TO START"
            font="Inter" size={72} weight={800}
            color="#E2E8F0" opacity={0.95}
            letterSpacing={5}
            x={960} y={500} align="center" />
        </FadeIn>
      </ScaleIn>
    </Sequence>

    {/* Fade out */}
    <Sequence from={75}>
      <FadeOut duration={15} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "sectionId": "where_to_start",
  "sectionNumber": 6,
  "sectionLabel": "PART 6",
  "title": "WHERE TO START",
  "backgroundColor": "#0A0F1A",
  "ghostElements": [
    { "shape": "codebase_tree", "color": "#334155", "style": "file_tree" }
  ],
  "narrationSegments": ["where_to_start_001"]
}
```

---
