[title:]

# Section 3.0: Part 3 Title Card

**Tool:** Remotion
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 13:00 – 13:04

## Visual Description
A bold title card introduces Part 3. The text "Part 3" fades in small above the main title "The Mold Has Three Parts", which types on letter-by-letter. A thin horizontal rule expands outward from center beneath the title. Three small icons — a wall, a document, and a gear — fade in below the rule in sequence, previewing the three components. Background is deep navy with a subtle radial gradient.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Deep navy (#0A1628) with radial gradient to (#122240) at center
- No grid lines

### Chart/Visual Elements
- Part label: "Part 3" — small caps, centered, positioned at y=360
- Main title: "The Mold Has Three Parts" — large, centered, positioned at y=440
- Horizontal rule: 2px line, white at 40% opacity, centered at y=520, expands from 0px to 480px width
- Three preview icons at y=580, spaced 160px apart (centered at x=800, 960, 1120):
  - Wall icon: Simplified brick wall outline, `#D9944A` at 0.5 opacity, 28px
  - Document icon: Simplified page/spec outline, `#4A90D9` at 0.5 opacity, 28px
  - Gear icon: Simplified cog outline, `#5AAA6E` at 0.5 opacity, 28px

### Animation Sequence
1. **Frame 0–15 (0–0.5s):** Background fades in from black. "Part 3" fades in with slight upward drift (10px).
2. **Frame 15–60 (0.5–2.0s):** Main title types on character-by-character with a blinking cursor. Monospaced typing cadence (~30ms per character).
3. **Frame 60–75 (2.0–2.5s):** Cursor blinks twice, then disappears. Horizontal rule expands outward from center.
4. **Frame 75–105 (2.5–3.5s):** Three icons fade in left-to-right with 10-frame stagger. Each icon scales up from 0.8→1.0 with slight bounce.
5. **Frame 105–120 (3.5–4.0s):** Hold. All elements at full opacity. Gentle pulse on the rule (opacity 40%→60%→40%).

### Typography
- Part label: Inter Medium, 20px, #8B9DC3 (muted blue-gray), letter-spacing 4px, uppercase
- Main title: Inter Bold, 52px, #FFFFFF, letter-spacing -0.5px
- Typing cursor: 3px wide, #4A90D9, blinking 500ms interval

### Easing
- Fade in: `easeOutCubic`
- Title type-on: linear (constant typing speed)
- Rule expansion: `easeInOutCubic`
- Icon fade/scale: `spring({ damping: 14, stiffness: 120 })`

## Narration Sync
> "Now let's get precise. Because 'prompt is the mold' is a nice metaphor, but it's incomplete."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <AbsoluteFill style={{ background: 'radial-gradient(circle, #122240, #0A1628)' }}>
    <Sequence from={0} durationInFrames={15}>
      <FadeIn>
        <PartLabel text="Part 3" />
      </FadeIn>
    </Sequence>
    <Sequence from={15} durationInFrames={45}>
      <TypeOnText text="The Mold Has Three Parts" />
    </Sequence>
    <Sequence from={60} durationInFrames={15}>
      <ExpandingRule width={480} />
    </Sequence>
    <Sequence from={75} durationInFrames={30}>
      <StaggeredIcons
        icons={[
          { type: "wall", color: "#D9944A" },
          { type: "document", color: "#4A90D9" },
          { type: "gear", color: "#5AAA6E" },
        ]}
        stagger={10}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "partNumber": 3,
  "title": "The Mold Has Three Parts",
  "icons": [
    { "type": "wall", "label": "Tests", "color": "#D9944A" },
    { "type": "document", "label": "Prompt", "color": "#4A90D9" },
    { "type": "gear", "label": "Grounding", "color": "#5AAA6E" }
  ]
}
```

---
