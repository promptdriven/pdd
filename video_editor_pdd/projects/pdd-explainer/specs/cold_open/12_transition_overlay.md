[title:]

# Section 0.12: Transition Overlay — "Now Let Me Show You WHY This Matters"

**Tool:** Title
**Duration:** ~3s (90 frames @ 30fps)
**Timestamp:** 0:46 - 0:49

## Visual Description

A subtle text overlay that lands after the test-fix demo. The all-green test results from spec 11 remain visible but dim. A single line of text fades in, centered: "Now let me show you WHY this matters." The word "WHY" is emphasized — slightly larger, or in the accent blue color — while the rest of the sentence is in subdued off-white.

This is a bridge beat. It signals the transition from "here's what PDD does" to "here's why it's inevitable" — setting up Part 1: The Economics of Darning.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Previous test results dimmed to 15% opacity, overlaid with `#0A0F1A` at 0.85
- No grid lines

### Chart/Visual Elements

#### Dimming Overlay
- `#0A0F1A` at 0.85, full canvas
- Fades in over the test results

#### Text
- "Now let me show you" — Inter, 36px, regular (400), `#94A3B8` at 0.8, centered at y: 510
- "WHY" — Inter, 42px, bold (700), `#4A90D9`, inline within the sentence
- "this matters." — Inter, 36px, regular (400), `#94A3B8` at 0.8

Full rendered line: "Now let me show you **WHY** this matters."

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Dimming overlay fades in over test results.
2. **Frame 15-40 (0.5-1.33s):** Text fades in with a subtle 3px upward slide. "WHY" pulses once with a blue glow.
3. **Frame 40-75 (1.33-2.5s):** Hold. Text visible.
4. **Frame 75-90 (2.5-3s):** Everything fades to black — transitioning to Part 1.

### Typography
- Sentence text: Inter, 36px, regular (400), `#94A3B8` at 0.8
- "WHY": Inter, 42px, bold (700), `#4A90D9`
- "WHY" glow: `0 0 30px rgba(74, 144, 217, 0.3)`

### Easing
- Dimming overlay: `easeOut(quad)` over 15 frames
- Text fade-in: `easeOut(quad)` over 20 frames
- Text slide-up: `easeOut(cubic)` over 20 frames
- "WHY" glow pulse: `easeInOut(sine)` over 20 frames
- Final fade-out: `easeIn(quad)` over 15 frames

## Narration Sync
> "Now, let me show you why this matters."

Segment: `cold_open_010`

- **46.02s** (seg 010): Overlay fades in — "Now, let me show you"
- **47.50s**: "WHY" emphasis — "why this matters"
- **48.90s** (seg 010 ends): Fade to black, transition to Part 1

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={90}>
  {/* Dimming overlay */}
  <Sequence from={0}>
    <FadeIn duration={15}>
      <AbsoluteFill style={{ backgroundColor: 'rgba(10, 15, 26, 0.85)' }} />
    </FadeIn>
  </Sequence>

  {/* Transition text */}
  <Sequence from={15}>
    <SlideUp distance={3} duration={20}>
      <FadeIn duration={20}>
        <AbsoluteFill style={{ display: 'flex', justifyContent: 'center', alignItems: 'center' }}>
          <span style={{ fontFamily: 'Inter', fontSize: 36, color: 'rgba(148,163,184,0.8)' }}>
            Now let me show you{' '}
            <span style={{ fontSize: 42, fontWeight: 700, color: '#4A90D9' }}>WHY</span>
            {' '}this matters.
          </span>
        </AbsoluteFill>
      </FadeIn>
    </SlideUp>
  </Sequence>

  {/* "WHY" glow pulse */}
  <Sequence from={20} durationInFrames={20}>
    <GlowPulse target="WHY" color="#4A90D9" radius={30}
      peakOpacity={0.3} easing="easeInOutSine" />
  </Sequence>

  {/* Fade to black */}
  <Sequence from={75}>
    <FadeIn duration={15}>
      <AbsoluteFill style={{ backgroundColor: '#000000' }} />
    </FadeIn>
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "transition_overlay",
  "text": "Now let me show you WHY this matters.",
  "emphasis": { "word": "WHY", "color": "#4A90D9", "weight": 700 },
  "transitionTo": "part1_economics",
  "narrationSegments": ["cold_open_010"]
}
```

---
