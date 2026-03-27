[Remotion]

# Section 6.6: No Big Bang Callout — Key Insight

**Tool:** Remotion
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 0:24 - 0:29

## Visual Description

A text-forward insight card overlays the partially-migrated codebase grid. Three short statements stack vertically with staggered reveals, echoing the narration cadence:

1. "No big bang." — appears first, bold, white
2. "No rewrite." — appears second, bold, white
3. "Just gradual migration." — appears third, slightly different: semi-bold, green accent

Each line has a subtle horizontal rule that draws from left to right beneath it. The third line's rule is green instead of slate, emphasizing the positive framing.

Behind the text, the module grid from spec 05 remains faintly visible — the green-glowing modules provide a visual anchor for "gradual migration."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black) with module grid at 0.08 opacity
- Text overlay area: centered

### Chart/Visual Elements

#### Text Stack
- Position: centered at (960, 480), left-aligned within a 600px container
- Line 1: "No big bang." — Inter, 40px, bold (700), `#E2E8F0`
- Line 2: "No rewrite." — Inter, 40px, bold (700), `#E2E8F0`
- Line 3: "Just gradual migration." — Inter, 40px, semi-bold (600), `#5AAA6E`
- Line spacing: 70px between baselines

#### Horizontal Rules
- Below each line, offset 10px
- Lines 1-2: 250px wide, 1.5px, `#334155` at 0.4
- Line 3: 350px wide, 1.5px, `#5AAA6E` at 0.5

#### Background Module Grid
- Same grid from spec 05, but at 0.08 global opacity
- Green-glowing modules still faintly visible
- Creates depth without distraction

### Animation Sequence
1. **Frame 0-30 (0-1s):** Background grid dims to 0.08. Clean space for text.
2. **Frame 30-55 (1-1.83s):** "No big bang." fades in with 15px left-to-right slide. Rule draws beneath.
3. **Frame 55-80 (1.83-2.67s):** "No rewrite." fades in same way. Rule draws beneath.
4. **Frame 80-110 (2.67-3.67s):** "Just gradual migration." fades in. Green rule draws, slightly longer.
5. **Frame 110-150 (3.67-5s):** Hold. All three lines visible. Green rule pulses once subtly.

### Typography
- Statement lines: Inter, 40px, bold (700), `#E2E8F0`
- Accent line: Inter, 40px, semi-bold (600), `#5AAA6E`
- Rules: respective colors

### Easing
- Text slide-in: `easeOut(cubic)` over 20 frames
- Rule draw: `easeOut(quad)` over 15 frames
- Background dim: `easeInOut(quad)` over 30 frames
- Green rule pulse: `easeInOut(sine)` single cycle, 30 frames

## Narration Sync
> "Just a gradual migration of where value lives — from code to specification."

Segment: `where_to_start_002` (final portion, ~24.00s - 29.88s)

- **24.00s**: "No big bang" appears
- **25.50s**: "No rewrite" appears
- **27.00s**: "Just gradual migration" appears
- **29.88s** (seg 002 ends): All three lines held

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* Dimmed module grid background */}
    <Opacity value={0.08}>
      <ModuleGridFromSpec05 />
    </Opacity>

    {/* Statement stack */}
    <AbsoluteFill style={{ justifyContent: 'center', alignItems: 'center' }}>
      <div style={{ width: 600 }}>

        {/* Line 1 */}
        <Sequence from={30}>
          <SlideRight distance={15} duration={20}>
            <FadeIn duration={20}>
              <Text text="No big bang." font="Inter" size={40}
                weight={700} color="#E2E8F0" />
            </FadeIn>
          </SlideRight>
          <Sequence from={20}>
            <DrawLine from={[0, 0]} to={[250, 0]}
              color="#334155" opacity={0.4} width={1.5}
              drawDuration={15} />
          </Sequence>
        </Sequence>

        {/* Line 2 */}
        <Sequence from={55}>
          <SlideRight distance={15} duration={20}>
            <FadeIn duration={20}>
              <Text text="No rewrite." font="Inter" size={40}
                weight={700} color="#E2E8F0" />
            </FadeIn>
          </SlideRight>
          <Sequence from={20}>
            <DrawLine from={[0, 0]} to={[250, 0]}
              color="#334155" opacity={0.4} width={1.5}
              drawDuration={15} />
          </Sequence>
        </Sequence>

        {/* Line 3 (green accent) */}
        <Sequence from={80}>
          <SlideRight distance={15} duration={20}>
            <FadeIn duration={20}>
              <Text text="Just gradual migration." font="Inter" size={40}
                weight={600} color="#5AAA6E" />
            </FadeIn>
          </SlideRight>
          <Sequence from={20}>
            <DrawLine from={[0, 0]} to={[350, 0]}
              color="#5AAA6E" opacity={0.5} width={1.5}
              drawDuration={15} />
          </Sequence>
        </Sequence>

      </div>
    </AbsoluteFill>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "key_insight_card",
  "insightId": "no_big_bang",
  "statements": [
    { "text": "No big bang.", "color": "#E2E8F0", "weight": 700 },
    { "text": "No rewrite.", "color": "#E2E8F0", "weight": 700 },
    { "text": "Just gradual migration.", "color": "#5AAA6E", "weight": 600 }
  ],
  "narrationSegments": ["where_to_start_002"]
}
```

---
