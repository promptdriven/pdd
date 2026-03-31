[title:]

# Section 0.10: Transition Overlay — "Now Let Me Show You WHY"

**Tool:** Title
**Duration:** ~3s (90 frames @ 30fps)
**Timestamp:** 0:46 - 0:48

## Visual Description

The green test results from the previous spec are still faintly visible behind a darkening overlay. A subtle text overlay fades in — understated, almost conversational: **"Now let me show you WHY this matters."** The text is smaller than the title card from spec 07 — this isn't a section header, it's a pivot. A bridge from the cold open demo into the substance of the video.

The tone is: "You've seen the trick. Now here's why it's not a trick." The text holds for a beat, then fades to black, transitioning to Part 1.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Inherited from spec 09 (test results), dimming to `#0A0F1A`
- Final state: Full black for transition

### Chart/Visual Elements

#### Dark Overlay
- Full-screen `#0A0F1A`, opacity ramps from 0.0 to 0.85 over first 20 frames
- Allows green test results to bleed through briefly, then obscures them

#### Text Overlay
- Text: "Now let me show you WHY this matters."
- Position: centered at (960, 520)
- Font: Inter, 36px, Medium (500)
- Color: `#94A3B8` (muted gray-blue — understated, not bold)
- "WHY" is emphasized: Inter, 36px, Bold (700), `#E2E8F0` (brighter white)
- No text-shadow or glow — clean and quiet

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Dark overlay ramps up, dimming the test results beneath.
2. **Frame 20-40 (0.67-1.33s):** Text fades in, centered. "Now let me show you WHY this matters." The word "WHY" is slightly brighter/bolder.
3. **Frame 40-70 (1.33-2.33s):** Hold. The text sits quietly over the dark background.
4. **Frame 70-90 (2.33-3s):** Everything fades to full black. Clean transition to Part 1.

### Typography
- Main text: Inter, 36px, Medium (500), `#94A3B8`
- "WHY": Inter, 36px, Bold (700), `#E2E8F0`

### Easing
- Overlay ramp: `easeOut(quad)` over 20 frames
- Text fade-in: `easeOut(quad)` over 20 frames
- Final fade-to-black: `easeIn(quad)` over 20 frames

## Narration Sync
> "Now, let me show you why this matters."

Segment: `cold_open_010`

- **46.02s** (seg 010): Overlay begins dimming — "Now, let me show you"
- **47.5s**: "why this matters" — text fully visible
- **48.90s** (seg 010 ends): Fade to black, transition to Part 1

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={90}>
  {/* Dark overlay ramp */}
  <Sequence from={0} durationInFrames={90}>
    <FadeIn durationFrames={20}>
      <Overlay color="#0A0F1A" opacity={0.85} />
    </FadeIn>
  </Sequence>

  {/* Transition text */}
  <Sequence from={20} durationInFrames={50}>
    <FadeIn durationFrames={20}>
      <AbsoluteFill style={{
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center'
      }}>
        <span style={{
          fontFamily: 'Inter',
          fontSize: 36,
          fontWeight: 500,
          color: '#94A3B8'
        }}>
          Now let me show you{' '}
          <span style={{ fontWeight: 700, color: '#E2E8F0' }}>WHY</span>
          {' '}this matters.
        </span>
      </AbsoluteFill>
    </FadeIn>
  </Sequence>

  {/* Fade to black */}
  <Sequence from={70} durationInFrames={20}>
    <FadeIn durationFrames={20}>
      <Overlay color="#000000" opacity={1.0} />
    </FadeIn>
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "componentId": "transition_overlay_why",
  "durationFrames": 90,
  "fps": 30,
  "narrationSegments": ["cold_open_010"],
  "text": "Now let me show you WHY this matters.",
  "emphasis": { "word": "WHY", "weight": 700, "color": "#E2E8F0" },
  "inheritsBackground": "09_test_fix_cycle",
  "transitionsTo": "part1_economics"
}
```

---
