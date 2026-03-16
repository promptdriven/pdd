[title:]

# Section 1.0: Part 1 Title Card

**Tool:** Remotion
**Duration:** ~4s
**Timestamp:** 0:16 – 0:20

## Visual Description
A bold title card introduces the section. The text "Part 1" fades in small above the main title "The Economics of Darning", which types on letter-by-letter. A thin horizontal rule expands outward from center beneath the title. Background is deep navy with a subtle radial gradient toward the center.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Deep navy (#0A1628) with radial gradient to (#122240) at center
- No grid lines

### Chart/Visual Elements
- Part label: "Part 1" — small caps, centered, positioned at y=380
- Main title: "The Economics of Darning" — large, centered, positioned at y=460
- Horizontal rule: 2px line, white at 40% opacity, centered at y=540, expands from 0px to 400px width
- Subtle background texture: fine diagonal hatching at 3% opacity (#FFFFFF)

### Animation Sequence
1. **Frame 0–15 (0–0.5s):** Background fades in from black. "Part 1" fades in with slight upward drift (10px).
2. **Frame 15–60 (0.5–2s):** Main title types on character-by-character with a blinking cursor. Monospaced typing cadence (~30ms per character).
3. **Frame 60–75 (2–2.5s):** Cursor blinks twice, then disappears. Horizontal rule expands outward from center.
4. **Frame 75–120 (2.5–4s):** Hold. All elements at full opacity. Gentle pulse on the rule (opacity 40% → 60% → 40%).

### Typography
- Part label: Inter Medium, 20px, #8B9DC3 (muted blue-gray), letter-spacing 4px, uppercase
- Main title: Inter Bold, 56px, #FFFFFF, letter-spacing -0.5px
- Typing cursor: 3px wide, #4A90D9 (cool blue), blinking 500ms interval

### Easing
- Fade in: `easeOutCubic`
- Title type-on: linear (constant typing speed)
- Rule expansion: `easeInOutCubic`

## Narration Sync
> "Now, let me show you why this matters."

Segment: `part1_economics_004` (16.16s – 19.22s)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <AbsoluteFill style={{ background: 'radial-gradient(circle, #122240, #0A1628)' }}>
    <Sequence from={0} durationInFrames={15}>
      <FadeIn>
        <PartLabel text="Part 1" />
      </FadeIn>
    </Sequence>
    <Sequence from={15} durationInFrames={45}>
      <TypeOnText text="The Economics of Darning" />
    </Sequence>
    <Sequence from={60} durationInFrames={15}>
      <ExpandingRule />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "partNumber": 1,
  "title": "The Economics of Darning",
  "segmentId": "part1_economics_004"
}
```
