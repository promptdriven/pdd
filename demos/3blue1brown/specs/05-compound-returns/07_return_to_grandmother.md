# Section 5.7: Return to Grandmother -- Callback

**Tool:** Hybrid (Video + Remotion)
**Duration:** ~10 seconds
**Timestamp:** 19:30 - 19:40

## Visual Description

A callback to the 1950s grandmother and modern person with socks from the cold open and Part 1. The grandmother is darning socks in her warm, lamp-lit setting. A modern person is visible briefly with disposable socks. This time the footage carries a different emotional weight -- not introducing the analogy, but resolving it. A subtle Remotion overlay adds the text "The economics made it rational." which reinforces that darning was the RIGHT choice in 1950.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Video footage as base layer (full frame)
- Remotion text overlay on top

### Video Source

This section reuses footage from the cold open (Section 0) and/or Part 1 (Section 1.8). Options:

1. **Preferred:** Re-cut from existing cold open footage of the grandmother darning socks
   - Use a different angle or moment than the cold open if available
   - The grandmother at her lamp, needle and sock in hand
   - Warm incandescent lighting, 1950s setting

2. **Alternative:** New Veo 3.1 generation with the following prompt:

```
Close-up of a 1950s grandmother's hands carefully darning a wool sock by lamplight. Warm incandescent glow. Period-appropriate thimble and darning mushroom visible. The hands are skilled and practiced — this is a competent, economically rational person, not a quaint figure.

STYLE: Warm, respectful, slightly desaturated with amber tones. Cinematic shallow depth of field.

CAMERA: Slow push-in on hands. Intimate framing.

MOOD: Dignified. This was the right thing to do.

DURATION: 10 seconds
NO DIALOGUE, NO TEXT OVERLAYS
```

### Remotion Overlay Elements

1. **Text Overlay**
   - Text: "The economics made it rational."
   - Position: Lower third, centered
   - Font: Sans-serif, 28pt, white
   - Background: Semi-transparent dark strip (rgba(26, 26, 46, 0.7))
   - Padding: 12px vertical, 40px horizontal
   - Rounded corners: 4px

2. **Subtle Sepia/Warm Grade**
   - If the source footage is not already warm-toned, apply a Remotion color filter
   - Sepia: 20% overlay
   - Warmth: +10% amber shift
   - Slight vignette at edges

3. **Transition In**
   - Cross-dissolve from the investment table (5.6)
   - Duration: 30 frames (1 second)

### Animation Sequence

1. **Frame 0-30 (0-1s):** Cross-dissolve from investment table
   - Table fades out, grandmother footage fades in
   - Warm color shift takes effect

2. **Frame 30-150 (1-5s):** Grandmother darning
   - Full video footage visible
   - Camera slow push-in on hands (if Veo-generated)
   - The viewer recognizes this imagery from earlier

3. **Frame 150-210 (5-7s):** Text overlay appears
   - "The economics made it rational." fades in on dark strip
   - Clean, definitive statement

4. **Frame 210-300 (7-10s):** Hold
   - Grandmother continues darning
   - Text remains visible
   - The moment lands emotionally -- this was rational behavior, not foolishness

### Code Structure (Remotion)

```typescript
const ReturnToGrandmother: React.FC = () => {
  const frame = useCurrentFrame();

  // Cross-dissolve from previous section
  const videoOpacity = interpolate(
    frame, [0, 30], [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Text overlay
  const textOpacity = interpolate(
    frame, [150, 195], [0, 1],
    { extrapolateRight: 'clamp' }
  );

  return (
    <AbsoluteFill>
      {/* Grandmother video footage */}
      <Video
        src={grandmotherDarningClip}
        style={{
          width: '100%',
          height: '100%',
          objectFit: 'cover',
          opacity: videoOpacity,
          filter: 'sepia(0.2) saturate(0.9)',
        }}
      />

      {/* Warm vignette overlay */}
      <div style={{
        position: 'absolute',
        inset: 0,
        background: 'radial-gradient(ellipse at center, transparent 50%, rgba(26,26,46,0.4) 100%)',
        opacity: videoOpacity,
      }} />

      {/* Text overlay - lower third */}
      <div style={{
        position: 'absolute',
        bottom: 120,
        left: '50%',
        transform: 'translateX(-50%)',
        backgroundColor: 'rgba(26, 26, 46, 0.7)',
        padding: '12px 40px',
        borderRadius: 4,
        opacity: textOpacity,
      }}>
        <span style={{
          color: 'white',
          fontSize: 28,
          fontFamily: 'system-ui, sans-serif',
          fontStyle: 'italic',
        }}>
          The economics made it rational.
        </span>
      </div>
    </AbsoluteFill>
  );
};
```

### Easing

- Cross-dissolve: `easeInOutCubic`
- Text fade-in: `easeOutCubic`

## Narration Sync

> "Your great-grandmother wasn't stupid for darning socks. The economics made it rational."

- "Your great-grandmother" -- the grandmother footage is fully visible, the viewer recognizes the callback
- "wasn't stupid" -- important inflection point; the tone is respectful, not dismissive
- "The economics made it rational." -- the text overlay appears, reinforcing the spoken words

## Audio Notes

- Warm ambient tone (matches the 1950s footage)
- No jarring transition sounds -- the cross-dissolve should be smooth and quiet
- Optional: very faint crackle or record-player warmth (period-appropriate)
- The narration carries the emotional weight; the audio bed supports, not competes

## Visual Style Notes

- This callback must feel intentional and earned -- the viewer saw this imagery in the cold open and Part 1
- The recontextualization is key: the first time, it introduced the analogy; now it resolves it
- The text overlay "The economics made it rational." is the thesis of the entire economics argument applied to the past
- Warm, respectful tone throughout -- the grandmother is presented as competent, not quaint
- The shallow depth of field and warm lighting create intimacy
- This is a brief beat (10 seconds) -- don't overload it

## Continuity Notes

- Footage source: cold open (Section 0, specs `00-cold-open/`) and/or Part 1 (spec `01-economics/08_split_screen_sepia.md`)
- The grandmother's outfit, setting, and props should match the earlier appearances
- If using re-cut footage, choose a moment that feels different but continuous (e.g., a different hand position, a completed stitch)

## Transition

Dissolves directly into Section 5.8 where we return to the developer with Cursor.
