[title:]

# Section 6.7: No Big Bang Callout — Gradual Migration Takeaway

**Tool:** Title
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 23:52 - 23:57

## Visual Description

A clean text card delivers the section's core takeaway. The partially-converted codebase from the previous shot fades to a deep blur in the background — still visible as a ghost, the blue cluster a soft glow, but no longer the focus.

In the foreground, three lines of text appear sequentially, each on its own beat:

1. **"One module at a time."** — Clean, direct.
2. **"No big bang. No rewrite."** — Reassuring.
3. **"A gradual migration of where value lives — from code to specification."** — The conceptual payoff.

The third line uses the established color language: "code" is rendered in neutral gray, "specification" in glowing blue. A thin horizontal rule separates the first two lines (tactical) from the third (conceptual).

This is the last visual before the Closing section. It leaves the viewer with a clear, actionable mental model: start small, migrate gradually, value accumulates in the specification.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Ghost background: blurred codebase topology at 0.06 opacity, 30px Gaussian blur

### Chart/Visual Elements

#### Line 1
- "One module at a time." — Inter, 28px, semi-bold (600), `#E2E8F0` at 0.8
- Centered at y: 380

#### Line 2
- "No big bang. No rewrite." — Inter, 22px, regular (400), `#E2E8F0` at 0.5
- Centered at y: 430

#### Horizontal Rule
- 160px wide, 1.5px, `#334155` at 0.3
- Centered at y: 475

#### Line 3
- "A gradual migration of where value lives —" — Inter, 18px, regular (400), `#E2E8F0` at 0.4
- Centered at y: 520
- Second part on next line:
- "from **code** to **specification**." — Inter, 18px, regular (400)
- "code" in `#64748B` at 0.5 (neutral gray)
- "specification" in `#4A90D9` at 0.7 (glowing blue), with 8px text-shadow glow at `#4A90D9` at 0.15
- Centered at y: 555

#### Ghost Codebase
- Same topology from 06, blurred heavily (30px Gaussian)
- Overall opacity: 0.06
- Blue cluster visible as a warm smudge of `#4A90D9` at 0.03

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Previous shot's codebase blurs and dims to ghost state. Background settles.
2. **Frame 20-50 (0.67-1.67s):** Line 1 fades in with 8px upward slide: "One module at a time."
3. **Frame 50-75 (1.67-2.5s):** Line 2 fades in with 6px upward slide: "No big bang. No rewrite."
4. **Frame 75-90 (2.5-3s):** Horizontal rule draws from center outward.
5. **Frame 90-130 (3-4.33s):** Line 3 fades in — "code" appears in gray, then "specification" appears in blue with a subtle glow bloom.
6. **Frame 130-150 (4.33-5s):** Hold. All three lines visible. "specification" glow pulses once, gently.

### Typography
- Line 1: Inter, 28px, semi-bold (600), `#E2E8F0` at 0.8
- Line 2: Inter, 22px, regular (400), `#E2E8F0` at 0.5
- Line 3: Inter, 18px, regular (400), `#E2E8F0` at 0.4
- "code": `#64748B` at 0.5
- "specification": `#4A90D9` at 0.7, glow `#4A90D9` at 0.15

### Easing
- Background blur: `easeOut(quad)` over 20 frames
- Line 1 slide+fade: `easeOut(cubic)` over 20 frames
- Line 2 slide+fade: `easeOut(cubic)` over 18 frames
- Rule draw: `easeInOut(quad)` over 12 frames
- Line 3 fade: `easeOut(quad)` over 25 frames
- Glow bloom: `easeOut(cubic)` over 12 frames
- Final pulse: `easeInOut(sine)` single cycle, 20 frames

## Narration Sync
> "One module at a time. No big bang. No rewrite. Just a gradual migration of where value lives — from code to specification."

Segment: `where_to_start_003`

- **23:52** ("One module at a time"): Line 1 appears
- **23:54** ("No big bang. No rewrite."): Line 2 appears
- **23:55** ("Just a gradual migration"): Rule draws, line 3 begins
- **23:57** ("from code to specification"): "code" and "specification" colored, hold

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Ghost codebase background */}
    <Opacity value={0.06}>
      <GaussianBlur radius={30}>
        <CodebaseTopology blocks={allBlocks} edges={allEdges}
          convertedIndices={convertedModules}
          convertedGlow={{ color: '#4A90D9', opacity: 0.03 }} />
      </GaussianBlur>
    </Opacity>

    {/* Line 1 */}
    <Sequence from={20}>
      <SlideUp distance={8} duration={20}>
        <FadeIn duration={20}>
          <Text text="One module at a time." font="Inter" size={28}
            weight={600} color="#E2E8F0" opacity={0.8}
            x={960} y={380} align="center" />
        </FadeIn>
      </SlideUp>
    </Sequence>

    {/* Line 2 */}
    <Sequence from={50}>
      <SlideUp distance={6} duration={18}>
        <FadeIn duration={18}>
          <Text text="No big bang. No rewrite." font="Inter" size={22}
            weight={400} color="#E2E8F0" opacity={0.5}
            x={960} y={430} align="center" />
        </FadeIn>
      </SlideUp>
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={75}>
      <DrawLine from={[880, 475]} to={[1040, 475]}
        color="#334155" opacity={0.3} width={1.5}
        drawDuration={12} fromCenter />
    </Sequence>

    {/* Line 3 */}
    <Sequence from={90}>
      <FadeIn duration={25}>
        <Text text="A gradual migration of where value lives —"
          font="Inter" size={18} weight={400}
          color="#E2E8F0" opacity={0.4}
          x={960} y={520} align="center" />
      </FadeIn>
      <Sequence from={10}>
        <FadeIn duration={20}>
          <RichText x={960} y={555} align="center"
            font="Inter" size={18} weight={400}>
            from <Span color="#64748B" opacity={0.5}>code</Span>
            {' '}to{' '}
            <Span color="#4A90D9" opacity={0.7}
              glow={{ color: '#4A90D9', blur: 8, opacity: 0.15 }}>
              specification
            </Span>.
          </RichText>
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* Final pulse on "specification" */}
    <Sequence from={130}>
      <GlowPulse target="specification" color="#4A90D9"
        baseOpacity={0.15} peakOpacity={0.25}
        duration={20} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "callout_card",
  "lines": [
    { "text": "One module at a time.", "weight": 600, "size": 28 },
    { "text": "No big bang. No rewrite.", "weight": 400, "size": 22 },
    {
      "text": "A gradual migration of where value lives — from code to specification.",
      "weight": 400,
      "size": 18,
      "highlights": [
        { "word": "code", "color": "#64748B" },
        { "word": "specification", "color": "#4A90D9", "glow": true }
      ]
    }
  ],
  "ghostBackground": "codebase_topology_blurred",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["where_to_start_003"]
}
```

---
